/**
* Testing Shamir's IBS scheme(Sh-IBS) Program
*  A part of module are created by using and modifying the RSA program by GNU MP created by blanclus.
*  https://sehermitage.web.fc2.com/etc/gmp_src.html 	
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <gmp.h>
#include <time.h>
#include <openssl/sha.h>
#include <tepla/ec.h>
#define LOOP_N 10

extern void mpz_random_prime(mpz_ptr, int);
extern void mpz_random_prime2(mpz_ptr, mpz_ptr, mpz_ptr);
extern void mpz_ctomp(mpz_ptr, unsigned char *, unsigned int);
extern void mpz_mptoc(unsigned char *, unsigned int *, mpz_ptr);
extern void mpz_random_max(mpz_ptr, mpz_ptr);


int sha256_hash(char *message, char *hash){

	char digest[SHA256_DIGEST_LENGTH];
	SHA256_CTX sha_ctx;
	SHA256_Init(&sha_ctx); 
	SHA256_Update(&sha_ctx, message, strlen(message)); 
	SHA256_Final(digest, &sha_ctx); 
	strcpy(hash,digest);
    return 0;
}

void mpz_rand(mpz_t z, const mpz_t order)
{
    static gmp_randstate_t *state = NULL;

    if (state == NULL)
    {
        state = (gmp_randstate_t *)malloc(sizeof(gmp_randstate_t));
        gmp_randinit_default(*state);
        gmp_randseed_ui(*state, (int)time(NULL));
    }
    mpz_urandomm(z, *state, order);
}

void setup(EC_POINT MPK, EC_POINT P, mpz_ptr order, mpz_ptr s){

	mpz_rand(s, order);
	point_mul(MPK,s,P);

}

void key_derivation(mpz_ptr msk, char* id, EC_PAIRING p, EC_POINT S_id){

	EC_POINT Q_id;

	size_t len = strlen((char*)id);

	point_init(Q_id, p->g1);
	point_map_to_point(Q_id, id, len, 128);
	point_mul(S_id,msk,Q_id);
}

void signature_generation(EC_POINT USK, char* id, char* M, EC_POINT R, EC_POINT S, mpz_ptr order, EC_PAIRING p, EC_POINT P, mpz_ptr R_hash_mpz){
	mpz_t k, k_inv, M_hash_mpz;
	mpz_t tmp_R, tmp_M;
	size_t M_len = strlen((char*)M);
	size_t id_len = strlen((char*)id);
	unsigned char R_hash[SHA256_DIGEST_LENGTH];
	unsigned char M_hash[SHA256_DIGEST_LENGTH];
	EC_POINT H2M_P;
	EC_POINT H3R_SID;
	EC_POINT H2M_H3R;

	mpz_init(k);
	mpz_init(k_inv);
	mpz_init(M_hash_mpz);
	mpz_init(tmp_R);
	mpz_init(tmp_M);

	/* ① k <- Z*q */
	mpz_rand(k, order);

	/* ② R <- [k]P */
	point_mul(R,k,P);

	/* ③ S <- [k^-1]( [H2(M)]P + [H3(R)]S_id )*/
	mpz_invert(k_inv, k, order);

	size_t* size;
	unsigned char* R_byte;
	point_to_oct(R_byte, size, R);
	
	/* make H2(M) */
	sha256_hash(M, M_hash);
	mpz_ctomp(tmp_M, M_hash, SHA256_DIGEST_LENGTH);
	mpz_mod(M_hash_mpz, tmp_M, order);

	/* make H3(R) */
	sha256_hash(R_byte, R_hash);
	mpz_ctomp(tmp_R, R_hash, SHA256_DIGEST_LENGTH);
	mpz_mod(R_hash_mpz, tmp_R, order);

	/* For some reason, the operation does not work unless init is immediately before the operation... */
	point_init(H2M_P, p->g1);
	point_mul(H2M_P, M_hash_mpz, P);

	point_init(H3R_SID, p->g1);
	point_mul(H3R_SID, R_hash_mpz, USK);

	point_init(H2M_H3R, p->g1);
	point_add(H2M_H3R, H2M_P, H3R_SID);
	
	point_mul(S, k_inv, H2M_H3R);

	mpz_clear(k);
	mpz_clear(k_inv);
	mpz_clear(M_hash_mpz);
	mpz_clear(tmp_R);
	mpz_clear(tmp_M);
}

int signature_verification(EC_POINT MPK, char* id, char* M, EC_POINT R, EC_POINT S, mpz_ptr order, EC_PAIRING p, mpz_ptr R_hash_mpz){
	mpz_t M_hash_mpz;
	mpz_t tmp_R, tmp_M;
	int result;
	unsigned char R_hash[SHA256_DIGEST_LENGTH];
	unsigned char M_hash[SHA256_DIGEST_LENGTH];
	size_t len = strlen((char*)id);

	mpz_init(M_hash_mpz);
	mpz_init(tmp_R);
	mpz_init(tmp_M);

	EC_POINT Q_id;
	point_init(Q_id, p->g1);
	point_map_to_point(Q_id, id, len, 128);

	/* make H2(M) */
	sha256_hash(M, M_hash);
	mpz_ctomp(tmp_M, M_hash, SHA256_DIGEST_LENGTH);
	mpz_mod(M_hash_mpz, tmp_M, order);

	EC_POINT P1,P2,P3,P4,P5,P6;
	point_init(P1, p->g1);
	point_init(P2, p->g2);
	point_init(P3, p->g1);
	point_init(P4, p->g2);
	point_init(P5, p->g1);
	point_init(P6, p->g2);

	Element mock1, mock2, mock3;
	Element mock4, mock5, mock6;
	element_init(mock1, p->g3);
	element_init(mock2, p->g3);
	element_init(mock3, p->g3);
	element_init(mock4, p->g3);
	element_init(mock5, p->g3);
	element_init(mock6, p->g3);

	pairing_map(mock1, P1, P2, p);
	pairing_map(mock2, P3, P4, p);
	pairing_map(mock3, P5, P6, p);

	element_pow(mock4, mock2, M_hash_mpz);
	element_pow(mock5, mock3, R_hash_mpz);
	element_mul(mock6, mock4, mock5);

	result = element_cmp(mock1,mock6);

	mpz_clear(M_hash_mpz);
	mpz_clear(tmp_R);
	mpz_clear(tmp_M);

	return result;

}

int main(void){
	Field f;
	EC_GROUP ec;
	EC_PAIRING p;
    EC_POINT P1;
	EC_POINT P2;
	EC_POINT MPK;
	EC_POINT USK;
	EC_POINT R;
	EC_POINT S;
	Element g;
	mpz_t q, msk, order;
	mpz_t R_hash_mpz;
	char* id;
	char* message;
	id = "1234";
	message = "hogehoge";
	int b;
	clock_t gen_start, gen_end, gen_tmp, verif_start, verif_end, verif_tmp;

	/* initialization */
	pairing_init(p, "ECBN254a");

	gen_tmp = 0;
	verif_tmp = 0;

	printf("Paring-based IBS : Paterson's scheme\n");
	printf("This is an incomplete program. Some pairing values are inaccurate.\n");

	for(int i=1; i<=LOOP_N; i++){
		printf("*************************************[[[%d times]]]*************************************\n",i);
		point_init(P1, p->g1);
		point_init(P2, p->g2);
		point_init(MPK, p->g1);
		point_init(USK, p->g1);
		point_init(R, p->g1);
		point_init(S, p->g1);
		element_init(g, p->g3);

		mpz_init(q);
		mpz_init(msk);
		mpz_init(order);
		mpz_init(R_hash_mpz);

		/* setup */
		point_random(P1);
		printf("P1 ->");
		point_print(P1);

		mpz_set(order, *pairing_get_order(p));

		/* setup master key */
		setup(MPK, P1, order, msk);
		printf("MPK ->");
		point_print(MPK);

		/* key derivation */
		key_derivation(msk, id, p, USK);
		printf("USK ->");
		point_print(USK);

		/* signature generation */
		gen_start = clock();
		signature_generation(USK, id, message, R, S, order, p, P1, R_hash_mpz);
		gen_end = clock();
		gen_tmp += gen_end - gen_start;
		

		/* signature verification */
		verif_start = clock();
		b = signature_verification(MPK, id, message, R, S, order, p, R_hash_mpz);
		verif_end = clock();
		verif_tmp += verif_end - verif_start;
	}

	printf("signature generation : %f[msec]\n", ((double)gen_tmp/LOOP_N));

	printf("signature verification : %f[msec]\n", ((double)verif_tmp/LOOP_N));

	mpz_clear(q);
	mpz_clear(msk);
	mpz_clear(order);
	mpz_clear(R_hash_mpz);
	return 0;
}
