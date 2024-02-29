/*
 * Masking implementation of AES based on tiny-AES project
 * by Joachim Fontfreyde (jfontfreyde@census-labs.com)
 */ 

/* EDIT BY YAYAT

This is an implementation of the AES algorithm, specifically ECB, CTR and CBC mode.
Block size can be chosen in aes.h - available choices are AES128, AES192, AES256.

The implementation is verified against the test vectors in:
  National Institute of Standards and Technology Special Publication 800-38A 2001 ED

ECB-AES128
----------

  plain-text:
    6bc1bee22e409f96e93d7e117393172a
    ae2d8a571e03ac9c9eb76fac45af8e51
    30c81c46a35ce411e5fbc1191a0a52ef
    f69f2445df4f9b17ad2b417be66c3710

  key:
    2b7e151628aed2a6abf7158809cf4f3c

  resulting cipher
    3ad77bb40d7a3660a89ecaf32466ef97 
    f5d3d58503b9699de785895a96fdbaaf 
    43b1cd7f598ece23881b00e3ed030688 
    7b0c785e27e8ad3f8223207104725dd4 


NOTE:   String length must be evenly divisible by 16byte (str_len % 16 == 0)
        You should pad the end of the string with zeros if this is not the case.
        For AES192/256 the key size is proportionally larger.

*/

/*****************************************************************************/
/* Includes:                                                                 */
/*****************************************************************************/
#include <string.h> // CBC mode, for memset
#include <stdlib.h>
#include <time.h>

#include "aes.h"

/*****************************************************************************/
/* Defines:                                                                  */
/*****************************************************************************/
// The number of columns comprising a state in AES. This is a constant in AES. Value=4
// The number of columns comprising a state in AES. This is a constant in AES. Value=4
#define Nb 4
// The number of 32 bit words in a key.
#define Nk 4
// Key length in bytes [128 bit]
#define KEYLEN 16
// The number of rounds in AES Cipher.
#define Nr 10

// jcallan@github points out that declaring Multiply as a function
// reduces code size considerably with the Keil ARM compiler.
// See this link for more information: https://github.com/kokke/tiny-AES-C/pull/3

#define SECURE

/*****************************************************************************/
/* Private variables:                                                        */
/*****************************************************************************/
// state - array holding the intermediate results during decryption.
typedef uint8_t state_t[4][4];
static state_t* state;

// state mirror 


//yayat's guess me if you can algo
typedef uint8_t state_y[4][4];
static state_y* state_yat;

// The array that stores the round keys.
static uint8_t RoundKey[176];
static uint8_t RoundKeyMasked[176] = {0};
// The key input to the AES Program
static uint8_t* Key;
uint32_t g_seed;

// Protect the mask 
uint8_t mask_dummy1[10] = {0};
uint8_t mask_dummy2[10] = {0};


// The lookup-tables are marked const so they can be placed in read-only storage instead of RAM
// The numbers below can be computed dynamically trading ROM for RAM -
// This can be useful in (embedded) bootloader applications, where ROM is often limited.
AES_CONST_VAR uint8_t sbox[256] = {
    //0     1    2      3     4    5     6     7      8    9     A      B    C     D     E     F
    0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
    0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
    0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
    0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
    0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
    0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
    0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
    0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
    0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
    0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
    0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
    0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
    0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
    0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
    0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
    0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16};

AES_CONST_VAR uint8_t mul_02[256] = {
    0x00, 0x02, 0x04, 0x06, 0x08, 0x0a, 0x0c, 0x0e, 0x10, 0x12, 0x14, 0x16, 0x18, 0x1a, 0x1c, 0x1e,
    0x20, 0x22, 0x24, 0x26, 0x28, 0x2a, 0x2c, 0x2e, 0x30, 0x32, 0x34, 0x36, 0x38, 0x3a, 0x3c, 0x3e,
    0x40, 0x42, 0x44, 0x46, 0x48, 0x4a, 0x4c, 0x4e, 0x50, 0x52, 0x54, 0x56, 0x58, 0x5a, 0x5c, 0x5e,
    0x60, 0x62, 0x64, 0x66, 0x68, 0x6a, 0x6c, 0x6e, 0x70, 0x72, 0x74, 0x76, 0x78, 0x7a, 0x7c, 0x7e,
    0x80, 0x82, 0x84, 0x86, 0x88, 0x8a, 0x8c, 0x8e, 0x90, 0x92, 0x94, 0x96, 0x98, 0x9a, 0x9c, 0x9e,
    0xa0, 0xa2, 0xa4, 0xa6, 0xa8, 0xaa, 0xac, 0xae, 0xb0, 0xb2, 0xb4, 0xb6, 0xb8, 0xba, 0xbc, 0xbe,
    0xc0, 0xc2, 0xc4, 0xc6, 0xc8, 0xca, 0xcc, 0xce, 0xd0, 0xd2, 0xd4, 0xd6, 0xd8, 0xda, 0xdc, 0xde,
    0xe0, 0xe2, 0xe4, 0xe6, 0xe8, 0xea, 0xec, 0xee, 0xf0, 0xf2, 0xf4, 0xf6, 0xf8, 0xfa, 0xfc, 0xfe,
    0x1b, 0x19, 0x1f, 0x1d, 0x13, 0x11, 0x17, 0x15, 0x0b, 0x09, 0x0f, 0x0d, 0x03, 0x01, 0x07, 0x05,
    0x3b, 0x39, 0x3f, 0x3d, 0x33, 0x31, 0x37, 0x35, 0x2b, 0x29, 0x2f, 0x2d, 0x23, 0x21, 0x27, 0x25,
    0x5b, 0x59, 0x5f, 0x5d, 0x53, 0x51, 0x57, 0x55, 0x4b, 0x49, 0x4f, 0x4d, 0x43, 0x41, 0x47, 0x45,
    0x7b, 0x79, 0x7f, 0x7d, 0x73, 0x71, 0x77, 0x75, 0x6b, 0x69, 0x6f, 0x6d, 0x63, 0x61, 0x67, 0x65,
    0x9b, 0x99, 0x9f, 0x9d, 0x93, 0x91, 0x97, 0x95, 0x8b, 0x89, 0x8f, 0x8d, 0x83, 0x81, 0x87, 0x85,
    0xbb, 0xb9, 0xbf, 0xbd, 0xb3, 0xb1, 0xb7, 0xb5, 0xab, 0xa9, 0xaf, 0xad, 0xa3, 0xa1, 0xa7, 0xa5,
    0xdb, 0xd9, 0xdf, 0xdd, 0xd3, 0xd1, 0xd7, 0xd5, 0xcb, 0xc9, 0xcf, 0xcd, 0xc3, 0xc1, 0xc7, 0xc5,
    0xfb, 0xf9, 0xff, 0xfd, 0xf3, 0xf1, 0xf7, 0xf5, 0xeb, 0xe9, 0xef, 0xed, 0xe3, 0xe1, 0xe7, 0xe5};

AES_CONST_VAR uint8_t mul_03[256] = {
    0x00, 0x03, 0x06, 0x05, 0x0c, 0x0f, 0x0a, 0x09, 0x18, 0x1b, 0x1e, 0x1d, 0x14, 0x17, 0x12, 0x11,
    0x30, 0x33, 0x36, 0x35, 0x3c, 0x3f, 0x3a, 0x39, 0x28, 0x2b, 0x2e, 0x2d, 0x24, 0x27, 0x22, 0x21,
    0x60, 0x63, 0x66, 0x65, 0x6c, 0x6f, 0x6a, 0x69, 0x78, 0x7b, 0x7e, 0x7d, 0x74, 0x77, 0x72, 0x71,
    0x50, 0x53, 0x56, 0x55, 0x5c, 0x5f, 0x5a, 0x59, 0x48, 0x4b, 0x4e, 0x4d, 0x44, 0x47, 0x42, 0x41,
    0xc0, 0xc3, 0xc6, 0xc5, 0xcc, 0xcf, 0xca, 0xc9, 0xd8, 0xdb, 0xde, 0xdd, 0xd4, 0xd7, 0xd2, 0xd1,
    0xf0, 0xf3, 0xf6, 0xf5, 0xfc, 0xff, 0xfa, 0xf9, 0xe8, 0xeb, 0xee, 0xed, 0xe4, 0xe7, 0xe2, 0xe1,
    0xa0, 0xa3, 0xa6, 0xa5, 0xac, 0xaf, 0xaa, 0xa9, 0xb8, 0xbb, 0xbe, 0xbd, 0xb4, 0xb7, 0xb2, 0xb1,
    0x90, 0x93, 0x96, 0x95, 0x9c, 0x9f, 0x9a, 0x99, 0x88, 0x8b, 0x8e, 0x8d, 0x84, 0x87, 0x82, 0x81,
    0x9b, 0x98, 0x9d, 0x9e, 0x97, 0x94, 0x91, 0x92, 0x83, 0x80, 0x85, 0x86, 0x8f, 0x8c, 0x89, 0x8a,
    0xab, 0xa8, 0xad, 0xae, 0xa7, 0xa4, 0xa1, 0xa2, 0xb3, 0xb0, 0xb5, 0xb6, 0xbf, 0xbc, 0xb9, 0xba,
    0xfb, 0xf8, 0xfd, 0xfe, 0xf7, 0xf4, 0xf1, 0xf2, 0xe3, 0xe0, 0xe5, 0xe6, 0xef, 0xec, 0xe9, 0xea,
    0xcb, 0xc8, 0xcd, 0xce, 0xc7, 0xc4, 0xc1, 0xc2, 0xd3, 0xd0, 0xd5, 0xd6, 0xdf, 0xdc, 0xd9, 0xda,
    0x5b, 0x58, 0x5d, 0x5e, 0x57, 0x54, 0x51, 0x52, 0x43, 0x40, 0x45, 0x46, 0x4f, 0x4c, 0x49, 0x4a,
    0x6b, 0x68, 0x6d, 0x6e, 0x67, 0x64, 0x61, 0x62, 0x73, 0x70, 0x75, 0x76, 0x7f, 0x7c, 0x79, 0x7a,
    0x3b, 0x38, 0x3d, 0x3e, 0x37, 0x34, 0x31, 0x32, 0x23, 0x20, 0x25, 0x26, 0x2f, 0x2c, 0x29, 0x2a,
    0x0b, 0x08, 0x0d, 0x0e, 0x07, 0x04, 0x01, 0x02, 0x13, 0x10, 0x15, 0x16, 0x1f, 0x1c, 0x19, 0x1a};
	
AES_CONST_VAR uint8_t sbox_yat[256] =   {
  //0     1    2      3     4    5     6     7      8    9     A      B    C     D     E     F
  0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a,
  0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a,
  0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a,
  0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a,
  0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a,
  0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a,
  0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a,
  0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a,
  0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a,
  0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a,
  0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a,
  0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a,
  0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a,
  0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a,
  0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a,
  0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a, 0xa5, 0x5a };
	
// The round constant word array, Rcon[i], contains the values given by
// x to the power (i-1) being powers of x (x is denoted as {02}) in the field GF(2^8)
static const uint8_t Rcon[11] = {
    0x8d, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36};

static uint8_t SboxMasked[256];

static uint8_t getSBoxValue(uint8_t num)
{
	return sbox[num];
}

static void calcMixColmask(uint8_t mask[10])
{
  mask_dummy1[6] = mul_02[mask_dummy1[0]] ^ mul_03[mask_dummy1[1]] ^ mask_dummy1[2]         ^ mask_dummy1[3];
  mask_dummy2[6] = mul_02[mask_dummy2[0]] ^ mul_03[mask_dummy2[1]] ^ mask_dummy2[2]         ^ mask_dummy2[3];
  mask[6] = mul_02[mask[0]] ^ mul_03[mask[1]] ^ mask[2]         ^ mask[3];
  
  mask_dummy1[7] = mask_dummy1[0]         ^ mul_02[mask_dummy1[1]] ^ mul_03[mask_dummy1[2]] ^ mask_dummy1[3];
  mask[7] = mask[0]         ^ mul_02[mask[1]] ^ mul_03[mask[2]] ^ mask[3];
  mask_dummy2[7] = mask_dummy2[0]         ^ mul_02[mask_dummy2[1]] ^ mul_03[mask_dummy2[2]] ^ mask_dummy2[3];
  
  mask[8] = mask[0]         ^ mask[1]         ^ mul_02[mask[2]] ^ mul_03[mask[3]];
  mask_dummy1[8] = mask_dummy1[0]         ^ mask_dummy1[1]         ^ mul_02[mask_dummy1[2]] ^ mul_03[mask_dummy1[3]];
  mask_dummy2[8] = mask_dummy2[0]         ^ mask_dummy2[1]         ^ mul_02[mask_dummy2[2]] ^ mul_03[mask_dummy2[3]];
  
  mask_dummy2[9] = mul_03[mask_dummy2[0]] ^ mask_dummy2[1]         ^ mask_dummy2[2]         ^ mul_02[mask_dummy2[3]];
  mask_dummy1[9] = mul_03[mask_dummy1[0]] ^ mask_dummy1[1]         ^ mask_dummy1[2]         ^ mul_02[mask_dummy1[3]];
  mask[9] = mul_03[mask[0]] ^ mask[1]         ^ mask[2]         ^ mul_02[mask[3]];
}

static void remask(state_t * s, uint8_t m1, uint8_t m2, uint8_t m3, uint8_t m4, uint8_t m5, uint8_t m6, uint8_t m7, uint8_t m8)
{
  for (uint8_t i = 0; i < 4; i++)
  {
    (*s)[i][0] = (*s)[i][0] ^ (m1 ^ m5);
    (*s)[i][1] = (*s)[i][1] ^ (m2 ^ m6);
    (*s)[i][2] = (*s)[i][2] ^ (m3 ^ m7);
    (*s)[i][3] = (*s)[i][3] ^ (m4 ^ m8);
  }
}

//Calculate the the invSbox to change from Mask m to Mask m'
static void calcSboxMasked(uint8_t mask[10])
{
  for (int i = 0; i < 256; i++){
    SboxMasked[i ^ mask[4]] = sbox[i] ^ mask[5];
  }
}

// The SubBytes Function Substitutes the values in the
// state matrix with values in an masked S-box.
static void SubBytesMasked(void)
{
  uint8_t i, j;
  for (i = 0; i < 4; ++i)
  {
    for (j = 0; j < 4; ++j)
    {
      (*state)[j][i] = SboxMasked[(*state)[j][i]];
    }
  }
}

// This function adds the masked round key to state.
// The round key is added to the state by an XOR function.
static void AddRoundKeyMasked(uint8_t round) //, const uint8_t* RoundKey)
{
  uint8_t i, j;
  for(i = 0; i < 4; i++){
    for (j = 0; j < 4; ++j)
    {
      (*state)[i][j] ^= RoundKeyMasked[(round * Nb * 4) + (i * Nb) + j];
    }
  }
}


// This function produces Nb(Nr+1) round keys. The round keys are used in each round to decrypt the states.
static void KeyExpansion(void)
{
  unsigned i, j, k;
  uint8_t tempa[4]; // Used for the column/row operations

  // The first round key is the key itself.
  for (i = 0; i < Nk; ++i)
  {
    RoundKey[(i * 4) + 0] = Key[(i * 4) + 0];
    RoundKey[(i * 4) + 1] = Key[(i * 4) + 1];
    RoundKey[(i * 4) + 2] = Key[(i * 4) + 2];
    RoundKey[(i * 4) + 3] = Key[(i * 4) + 3];
  }

  // All other round keys are found from the previous round keys.
  for (i = Nk; i < Nb * (Nr + 1); ++i)
  {
    {
      k = (i - 1) * 4;
      tempa[0] = RoundKey[k + 0];
      tempa[1] = RoundKey[k + 1];
      tempa[2] = RoundKey[k + 2];
      tempa[3] = RoundKey[k + 3];
    }

    if (i % Nk == 0)
    {
      // This function shifts the 4 bytes in a word to the left once.
      // [a0,a1,a2,a3] becomes [a1,a2,a3,a0]

      // Function RotWord()
      {
        const uint8_t u8tmp = tempa[0];
        tempa[0] = tempa[1];
        tempa[1] = tempa[2];
        tempa[2] = tempa[3];
        tempa[3] = u8tmp;
      }

      // SubWord() is a function that takes a four-byte input word and
      // applies the S-box to each of the four bytes to produce an output word.

      // Function Subword()
      {
        tempa[0] = getSBoxValue(tempa[0]);
        tempa[1] = getSBoxValue(tempa[1]);
        tempa[2] = getSBoxValue(tempa[2]);
        tempa[3] = getSBoxValue(tempa[3]);
      }

      tempa[0] = tempa[0] ^ Rcon[i / Nk];
    }
    j = i * 4;
    k = (i - Nk) * 4;
    RoundKey[j + 0] = RoundKey[k + 0] ^ tempa[0];
    RoundKey[j + 1] = RoundKey[k + 1] ^ tempa[1];
    RoundKey[j + 2] = RoundKey[k + 2] ^ tempa[2];
    RoundKey[j + 3] = RoundKey[k + 3] ^ tempa[3];
  }
}

// This function adds the round key to state.
// The round key is added to the state by an XOR function.
#ifndef SECURE
static void AddRoundKey(uint8_t round)
{
  uint8_t i, j;
  for (i = 0; i < 4; ++i)
  {
    for (j = 0; j < 4; ++j)
    {
      (*state)[i][j] ^= RoundKey[(round * Nb * 4) + (i * Nb) + j];
    }
  }
}
#endif

// The SubBytes Function Substitutes the values in the
// state matrix with values in an S-box.
#ifndef SECURE 
static void SubBytes(void)
{
  uint8_t i, j;
  for (i = 0; i < 4; ++i)
  {
    for (j = 0; j < 4; ++j)
    {
      (*state)[j][i] = getSBoxValue((*state)[j][i]);
    }
  }
}
#endif

// The ShiftRows() function shifts the rows in the state to the left.
// Each row is shifted with different offset.
// Offset = Row number. So the first row is not shifted.
static void ShiftRows(void)
{
  uint8_t temp;

  // Rotate first row 1 columns to left
  temp 			 = (*state)[0][1];
  (*state)[0][1] = (*state)[1][1];
  (*state)[1][1] = (*state)[2][1];
  (*state)[2][1] = (*state)[3][1];
  (*state)[3][1] = temp;

  // Rotate second row 2 columns to left
  temp 			 = (*state)[0][2];
  (*state)[0][2] = (*state)[2][2];
  (*state)[2][2] = temp;

  temp 			 = (*state)[1][2];
  (*state)[1][2] = (*state)[3][2];
  (*state)[3][2] = temp;

  // Rotate third row 3 columns to left
  temp 			 = (*state)[0][3];
  (*state)[0][3] = (*state)[3][3];
  (*state)[3][3] = (*state)[2][3];
  (*state)[2][3] = (*state)[1][3];
  (*state)[1][3] = temp;
}

static uint8_t xtime(uint8_t x)
{
  return ((x << 1) ^ (((x >> 7) & 1) * 0x1b));
}

// MixColumns function mixes the columns of the state matrix
static void MixColumns(void)
{
	uint8_t temp[4];
    uint8_t i;
    for (i = 0; i < 4; i++) {
        temp[0] = (*state)[i][0];
        temp[1] = (*state)[i][1];
        temp[2] = (*state)[i][2];
        temp[3] = (*state)[i][3];

        (*state)[i][0] = xtime(temp[0] ^ temp[1]) ^ temp[1] ^ temp[2] ^ temp[3];
        (*state)[i][1] = temp[0] ^ xtime(temp[1] ^ temp[2]) ^ temp[2] ^ temp[3];
        (*state)[i][2] = temp[0] ^ temp[1] ^ xtime(temp[2] ^ temp[3]) ^ temp[3];
        (*state)[i][3] = xtime(temp[0] ^ temp[3]) ^ temp[0] ^ temp[1] ^ temp[2];
    }
}
// MixColumns ghost
static void MixColumnsGhost(void)
{
	uint8_t temp[4];
    uint8_t i;
    for (i = 0; i < 4; i++) {
        temp[0] = (*state_yat)[i][0];
        temp[1] = (*state_yat)[i][1];
        temp[2] = (*state_yat)[i][2];
        temp[3] = (*state_yat)[i][3];

        (*state_yat)[i][0] = xtime(temp[0] ^ temp[1]) ^ temp[1] ^ temp[2] ^ temp[3];
        (*state_yat)[i][1] = temp[0] ^ xtime(temp[1] ^ temp[2]) ^ temp[2] ^ temp[3];
        (*state_yat)[i][2] = temp[0] ^ temp[1] ^ xtime(temp[2] ^ temp[3]) ^ temp[3];
        (*state_yat)[i][3] = xtime(temp[0] ^ temp[3]) ^ temp[0] ^ temp[1] ^ temp[2];
    }
}

static uint8_t generateRandom(void) {
    g_seed = (214013 * g_seed + 2531011);
    return (g_seed >> 16) & 0x7FFF;
}

void delay(int number_of_seconds)
{
    // Converting time into milli_seconds
    int milli_seconds = 1000 * number_of_seconds;
    // Storing start time
    clock_t start_time = clock();
    // looping till required time is not achieved
    while (clock() < start_time + milli_seconds);
}
 
static void Gen_delay(uint8_t level)
{
    for(int i = 0; i < level; i++)
	{
		delay(10);
	}
}
	
static void InitMaskingEncrypt(uint8_t mask[10])
{
	uint8_t int_rand1 = (uint8_t)((*state)[0][0] ^ (*state)[0][1] ^ (*state)[0][2] ^ (*state)[0][3]);
    uint8_t int_rand2 = (uint8_t)((*state)[1][0] ^ (*state)[1][1] ^ (*state)[1][2] ^ (*state)[1][3]);
    uint8_t int_rand3 = (uint8_t)((*state)[2][0] ^ (*state)[2][1] ^ (*state)[2][2] ^ (*state)[2][3]);
    uint8_t int_rand4 = (uint8_t)((*state)[3][0] ^ (*state)[3][1] ^ (*state)[3][2] ^ (*state)[3][3]);

    g_seed = (int_rand1 << 24) | (int_rand2 << 16) | (int_rand3 << 8) | (int_rand4);
	
	mask[4] = generateRandom();
	memcpy(RoundKeyMasked, RoundKey, 176);
	
	
	//Delay
	// Gen_delay(5);
	
	// V3
	for (uint8_t i = 2; i < 4; i++) {
        mask[i] = generateRandom();
    }
	
	for (uint8_t i = 0; i < 3; i++) 
	{
		mask_dummy1[i] = generateRandom();
	}
	mask[0] = generateRandom();
	for (uint8_t i = 0; i < 2; i++)
	{
		mask_dummy2[i] = generateRandom();
	}
	mask[1] = generateRandom();
	for (uint8_t i = 2; i < 4; i++)
	{
		mask_dummy2[i] = generateRandom();
	}
	for (uint8_t i = 3; i < 6; i++)
	{
		mask_dummy1[i] = generateRandom();
	}
	mask_dummy2[4] = generateRandom();
	// mask[5] = generateRandom();
	mask_dummy2[5] = generateRandom();
	
	//Calculate m1',m2',m3',m4'
	calcMixColmask(mask);
	mask[5] = generateRandom();
	//Delay 
	// Gen_delay(5);
	
	//Calculate the masked Sbox
	calcSboxMasked(mask); //m' -> m

	//Init masked key
	//	Last round mask M' to mask 0
	remask(state_yat, mask_dummy1[0], mask_dummy1[1], mask_dummy1[2], mask_dummy1[3], mask_dummy2[5], mask_dummy1[5], mask_dummy2[5], mask_dummy2[5]);
	remask((state_t *) &RoundKeyMasked[(Nr * Nb * 4)], 0, 0, 0, 0, mask[5], mask[5], mask[5], mask[5]);

	// Mask change from M1',M2',M3',M4' to M
	for (uint8_t i = 0; i < Nr; i++)
	{
		remask((state_t *) &RoundKeyMasked[(i * Nb * 4)], mask[6], mask[7], mask[8], mask[9], mask[4], mask[4], mask[4], mask[4]);
		remask(state_yat, mask_dummy1[6], mask_dummy1[7], mask_dummy1[8], mask_dummy1[9], mask[0], mask[0], mask[0], mask[0]);
	}
}

// Cipher is the main function that encrypts the PlainText.
static void CipherMasked(void)
{
  // uint8_t RoundKeyMasked[AES_keyExpSize] = {0};
  uint8_t mask[10] = {0};
  uint8_t round = 0;

  InitMaskingEncrypt(mask);

  //Plain text masked with m1',m2',m3',m4'
  remask(state, mask[6], mask[7], mask[8], mask[9], 0, 0, 0, 0);

  // Masks change from M1',M2',M3',M4' to M
  //AddRoundKeyMasked(0);
  {
	  
	  uint8_t i, j;
	  for(i = 0; i < 4; i++){
		for (j = 0; j < 4; ++j)
		{
		  (*state_yat)[j][i] ^= (RoundKeyMasked[(round * Nb * 4) + (i * Nb) + j] ^ 0xa5);
		  (*state)[i][j] ^= RoundKeyMasked[(round * Nb * 4) + (i * Nb) + j];
		}
	  }
  }
  
  // There will be Nr rounds.
  // The first Nr-1 rounds are identical.
  // These Nr rounds are executed in the loop below.
  // Last one without MixColumns()
  for (round = 1;; round++)
  {
    // Mask changes from M to M'
	if (round == 1 || round == 8 || round == 9 || round == 10)
	{
		uint8_t i, j;
		for (i = 0; i < 4; ++i)
		{
			// for (j = 0; j < 4; ++j)
			// {
				// (*state_yat)[j][i] = generateRandom();
				// (*state_yat)[j][i] ^= 0x5a;
				// (*state_yat)[j][i] = SboxMasked[(*state_yat)[j][i]];
				// (*state)[j][i] = SboxMasked[(*state)[j][i]];
			// }
			
			j = 0;
			{
				(*state_yat)[j][i] ^= 0x5a;
				(*state_yat)[j][i] = SboxMasked[(*state_yat)[j][i]];
				(*state_yat)[j][i] = generateRandom();
				(*state)[j][i] = SboxMasked[(*state)[j][i]];
			}
			
			j = 1;
			{
				(*state_yat)[j][i] = generateRandom();
				(*state_yat)[j][i] ^= 0x5a;
				(*state)[j][i] = SboxMasked[(*state)[j][i]];
				(*state_yat)[j][i] = SboxMasked[(*state_yat)[j][i]];
			}
			
			j = 2;
			{
				(*state_yat)[j][i] ^= 0x5a;
				(*state_yat)[j][i] = SboxMasked[(*state_yat)[j][i]];
				(*state)[j][i] = SboxMasked[(*state)[j][i]];
				(*state_yat)[j][i] = generateRandom();
			}
			
			j = 3;
			{
				(*state_yat)[j][i] ^= 0x5a;
				(*state_yat)[j][i] = SboxMasked[(*state_yat)[j][i]];
				(*state_yat)[j][i] = generateRandom();
				(*state)[j][i] = SboxMasked[(*state)[j][i]];	
			}
		}
	}
	else 
	{
		SubBytesMasked();	
	}
    //No impact on mask
	if (round  != 1 || round != 8 || round != 9 || round != 10)
	{
		uint8_t temp;
		uint8_t temp_yat;

		// Rotate first row 1 columns to left
		temp 			 = (*state)[0][1];
		(*state)[0][1] = (*state)[1][1];
		(*state)[1][1] = (*state)[2][1];
		(*state)[2][1] = (*state)[3][1];
		(*state)[3][1] = temp;
		
		temp_yat	   	   = (*state_yat)[0][1];
		(*state_yat)[0][1] = (*state_yat)[1][1];
		(*state_yat)[1][1] = (*state_yat)[2][1];
		(*state_yat)[2][1] = (*state_yat)[3][1];
		(*state_yat)[3][1] = temp_yat;
		
		

		// Rotate second row 2 columns to left
		temp 			 = (*state)[0][2];
		(*state)[0][2] = (*state)[2][2];
		(*state)[2][2] = temp;
		
		temp_yat 			 = (*state_yat)[0][2];
		(*state_yat)[0][2] = (*state_yat)[2][2];
		(*state_yat)[2][2] = temp_yat;

		temp 			 = (*state)[1][2];
		(*state)[1][2] = (*state)[3][2];
		(*state)[3][2] = temp;
		
		temp_yat 			 = (*state_yat)[1][2];
		(*state_yat)[1][2] = (*state_yat)[3][2];
		(*state_yat)[3][2] = temp_yat;

		// Rotate third row 3 columns to left
		temp 			 = (*state)[0][3];
		(*state)[0][3] = (*state)[3][3];
		(*state)[3][3] = (*state)[2][3];
		(*state)[2][3] = (*state)[1][3];
		(*state)[1][3] = temp;
		
		temp_yat 			 = (*state_yat)[0][3];
		(*state_yat)[0][3] = (*state_yat)[3][3];
		(*state_yat)[3][3] = (*state_yat)[2][3];
		(*state_yat)[2][3] = (*state_yat)[1][3];
		(*state_yat)[1][3] = temp_yat;
	}
	else 
	{
		ShiftRows();
	}
    
    if (round == Nr)
    {
      break;
    }
    //Change mask from M' to
    // M1 for first row
    // M2 for second row
    // M3 for third row
    // M4 for fourth row
    remask(state, mask[0], mask[1], mask[2], mask[3], mask[5], mask[5], mask[5], mask[5]);

    // Masks change from M1,M2,M3,M4 to M1',M2',M3',M4'
    MixColumns();

    // Add the First round key to the state before starting the rounds.
    // Masks change from M1',M2',M3',M4' to M
	if (round == 2 || round == 3 || round == 5 || round == 7)
	{
		{
			uint8_t i, j;
			for(i = 0; i < 4; i++)
			{
				for (j = 0; j < 4; ++j)
				{
					(*state_yat)[j][i] ^= (RoundKeyMasked[(round * Nb * 4) + (i * Nb) + j] ^ 0xa5);
					(*state)[i][j] ^= RoundKeyMasked[(round * Nb * 4) + (i * Nb) + j];
				}
			}
		}
	}
	else 
	{
		AddRoundKeyMasked(round);
	}
    
  }

  // Mask are removed by the last addroundkey
  // From M' to 0
  remask(state_yat, mask_dummy1[0], mask_dummy2[1], mask_dummy1[2], mask_dummy2[3], mask[4], mask[4], mask[4], mask[4]);
  MixColumnsGhost();
  AddRoundKeyMasked(Nr);
}

// Cipher is the main function that encrypts the PlainText.
#ifndef SECURE
static void Cipher(void)
{
  uint8_t round = 0;

  // Add the First round key to the state before starting the rounds.
  AddRoundKey(0);

  // There will be Nr rounds.
  // The first Nr-1 rounds are identical.
  // These Nr rounds are executed in the loop below.
  // Last one without MixColumns()
  for (round = 1;; ++round)
  {
    SubBytes();
    ShiftRows();
    if (round == Nr)
    {
      break;
    }
    MixColumns();
    AddRoundKey(round);
  }
  // Add round key to last round
  AddRoundKey(Nr);
}
#endif


void AES128_ECB_indp_setkey(uint8_t* key)
{
  Key = key;
  KeyExpansion();
}

void AES128_ECB_indp_crypto(uint8_t* input)
{
	state = (state_t*)input;
	
	state_yat = (state_y*)malloc(sizeof(state_y));
	// Check if memory allocation was successful
	if (state == NULL || state_yat == NULL)
	{
		return;
	}
	
	memcpy(state_yat, input, sizeof(state_y));
	
#ifdef SECURE 
	CipherMasked();
#else 
	Cipher();
#endif
	
	free(state_yat);
}