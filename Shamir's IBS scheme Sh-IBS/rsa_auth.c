/**
* Testing Shamir's IBS scheme(Sh-IBS) Program
*  This program and module are created by using and modifying the RSA program by GNU MP created by blanclus.
*  https://sehermitage.web.fc2.com/etc/gmp_src.html
*
 	* rsa_gmp.c
 	*  RSA Encrypt/Decrypt Program using GNU MP
 	*  written by blanclux
 	*  This software is distributed on an "AS IS" basis WITHOUT WARRANTY OF ANY KIND.
 	
*/

#include <stdio.h>
#include <string.h>
#include <gmp.h>
#include <openssl/sha.h>
#include <stdlib.h>
#include <time.h>

#define RSA_N_LEN	1024    /* RSA n key Length (bits) (must be even) */
#define RSA_E_LEN	5		/* RSA e key length (bits) ( > 2) */
#define LOOP_N 10

/*
 * Minimum bitsize of RSA key p, q and n.
 */
#define RSA_MIN_P  49
#define RSA_MIN_Q  49
#define RSA_MIN_N  (RSA_MIN_P + RSA_MIN_Q)

/*
 * RSA_KEY_DFB defines the upper limit of bit difference between P and Q.
 */
#define RSA_KEY_DFB  4

/*
 * Macros for readability
 */
#define rsa_encrypt( c, m, e, n )      mpz_powm( (c), (m), (e), (n) )
#define rsa_decrypt( m, c, d, n )      mpz_powm( (m), (c), (d), (n) )

extern void mpz_random_prime(mpz_ptr, int);
extern void mpz_random_prime2(mpz_ptr, mpz_ptr, mpz_ptr);
extern void mpz_ctomp(mpz_ptr, unsigned char *, unsigned int);
extern void mpz_mptoc(unsigned char *, unsigned int *, mpz_ptr);
extern void mpz_random_max(mpz_ptr, mpz_ptr);

static void
printHex(const char *title, const unsigned char *s, int len)
{
	int     n;
	printf("%s:", title);
	for (n = 0; n < len; ++n) {
		if ((n % 16) == 0) {
			printf("\n%04x", n);
		}
		printf(" %02x", s[n]);
	}
	printf("\n");
}

int
rsa_gen_pq(mpz_ptr n, mpz_ptr p, mpz_ptr q, int pb, int qb)
{
	int nb;
	mpz_t tp, tq, maxq, minq, tmp, tmp1;

	if (pb < RSA_MIN_P)
		return 1;
	if (qb < RSA_MIN_Q)
		return 1;

	mpz_init(tp);
	mpz_init(tq);
	mpz_init(maxq);
	mpz_init(minq);
	mpz_init(tmp);
	mpz_init(tmp1);

	nb = pb + qb;

	mpz_random_prime(tp, pb);	/* generate p */

	/* set maxq */
	mpz_set_ui(tmp, 0);
	mpz_setbit(tmp, nb);
	mpz_sub_ui(tmp, tmp, 1);	/* 2^nb - 1 */
	mpz_tdiv_q(maxq, tmp, tp);
	mpz_set_ui(tmp, 0);
	mpz_setbit(tmp, qb);		/* 2^qb */
	if (mpz_cmp(maxq, tmp) > 0) {
		mpz_set(maxq, tmp);			/* if maxq is larger than 2^qb, */
		mpz_sub_ui(maxq, maxq, 1);	/* let maxq 2^qb - 1 */
	}

	/* set minq */
	mpz_set_ui(tmp, 0);
	mpz_setbit(tmp, nb - 1);	/* 2 ^(nb-1) */
	mpz_tdiv_q(minq, tmp, tp);
	mpz_set_ui(tmp, 0);
	mpz_setbit(tmp, qb - 1);	/* 2 ^(qb-1) */
	if (mpz_cmp(minq, tmp) < 0) {	/* if minq is smaller than 2^(qb-1), */
		mpz_set(minq, tmp);			/* let minq 2^(qb-1) */
	}

	do {
		mpz_random_prime2(tq, maxq, minq);
		mpz_sub(tmp, tp, tq);
	} while (pb - mpz_sizeinbase(tmp, 2) > RSA_KEY_DFB);
	/* check if |p-q| is large enough */

	if (mpz_sgn(tmp) == -1 && pb == qb) {
		mpz_set(tmp1, tp);		/* if p is smaller than q and their bitsize is the same, */
		mpz_set(tp, tq);		/* exchange p and q. */
		mpz_set(tq, tmp1);		/* p should be larger than p generally */
	}

	mpz_mul(n, tp, tq);
	mpz_set(p, tp);
	mpz_set(q, tq);

	mpz_clear(tp);
	mpz_clear(tq);
	mpz_clear(maxq);
	mpz_clear(minq);
	mpz_clear(tmp);
	mpz_clear(tmp1);

	return 0;
}

int
rsa_gen_ed(mpz_ptr d, mpz_ptr e, int eb, mpz_ptr p, mpz_ptr q)
{
	mpz_t lm, p1, q1;
	int rv;

	if (eb < 2) {
		return 1;
	}

	mpz_init(lm);
	mpz_init_set(p1, p);
	mpz_sub_ui(p1, p1, 1);
	mpz_init_set(q1, q);
	mpz_sub_ui(q1, q1, 1);

	mpz_lcm(lm, p1, q1);		/* lm = lcm(p-1, q-1) */

	do {
		mpz_random_prime(e, eb);
		rv = mpz_invert(d, e, lm);	/* d = 1/e mod lm  */
	} while (!rv);

	if (mpz_sgn(d) == -1) {
		mpz_add(d, d, lm);
	}

	mpz_clear(lm);
	mpz_clear(p1);
	mpz_clear(q1);

	return 0;
}

int sha256_hash(char *message, char *hash){

	char digest[SHA256_DIGEST_LENGTH];
	SHA256_CTX sha_ctx;
	SHA256_Init(&sha_ctx); // Initialize context
	SHA256_Update(&sha_ctx, message, strlen(message)); // input : message
	SHA256_Final(digest, &sha_ctx); // output to digest
	strcpy(hash,digest); // copy to hash
    return 0;
}

int setup(mpz_ptr p, mpz_ptr q, mpz_ptr n, mpz_ptr d, mpz_ptr e, int pb, int qb, int eb){

	pb = qb = RSA_N_LEN / 2;
	eb = RSA_E_LEN;

	rsa_gen_pq(n, p, q, pb, qb);
	rsa_gen_ed(d, e, eb, p, q);

	return 0;
}

int key_derivation(mpz_ptr x,mpz_ptr n, mpz_ptr e, mpz_ptr d, char* id){
	mpz_t hash_mpz;
	char hash[SHA256_DIGEST_LENGTH];
	unsigned int hashLen;

	mpz_init(x);
	mpz_init(hash_mpz);

	sha256_hash(id,hash);

	mpz_ctomp(hash_mpz,hash,SHA256_DIGEST_LENGTH);
	
	mpz_powm(x,hash_mpz,d,n);

	mpz_clear(hash_mpz);
}

char* mpz_concat(mpz_ptr m1, unsigned char* m2, unsigned int m2_len){
	unsigned int size;
	unsigned char* tmp;
	unsigned char* result;
	size = (unsigned int)mpz_sizeinbase(m1, 10);
	tmp = (char *)malloc(size + 1);
	mpz_mptoc(tmp, &size, m1);
	strncat(tmp,m2, m2_len);
	return tmp;
}

int signature_generation(mpz_ptr T, mpz_ptr s, mpz_ptr n, mpz_ptr e, mpz_ptr x, unsigned char* m, unsigned int m_len){
	mpz_t t, c, t_c, tmp_mpz;
	unsigned char* tmp;
	unsigned int T_len, size;
	char hash[SHA256_DIGEST_LENGTH];

	mpz_init(t);
	mpz_init(c);
	mpz_init(t_c);
	mpz_init(tmp_mpz);

	/* from quotient ring */
	mpz_random_max(t,n);
	mpz_powm(T,t,e,n);

	/* concat */
	tmp = mpz_concat(T,m,m_len);
	/* hashing */
	sha256_hash(tmp, hash);
	mpz_ctomp(c,hash,SHA256_DIGEST_LENGTH);

	/* calculate s */
	mpz_powm(t_c, t, c, n);
	mpz_mul(tmp_mpz, x, t_c);
	mpz_mod(s, tmp_mpz, n);

	mpz_clear(t);
	mpz_clear(c);
	mpz_clear(t_c);
	mpz_clear(tmp_mpz);

	/* calc T,s done*/
	free(tmp);
	tmp = NULL;
	return 0;
}

int signature_verification(mpz_ptr n, mpz_ptr e, mpz_ptr d, char* id, unsigned char* m, unsigned int m_len, mpz_ptr T, mpz_ptr s){
	mpz_t s_e, T_c, c, calced, hid, hid_T_c;

	unsigned int size;
	int result;
	char hash[SHA256_DIGEST_LENGTH];
	char hash_id[SHA256_DIGEST_LENGTH];
	unsigned char* tmp;

	mpz_init(s_e);
	mpz_init(T_c);
	mpz_init(hid);
	mpz_init(calced);
	mpz_init(c);
	mpz_init(hid_T_c);

	/* s^e */
	mpz_powm(s_e, s, e, n);

	/* H(id)T^G(T||M) */

	/* concat T||M */
	tmp = mpz_concat(T,m,m_len);

	/* hashing c*/
	sha256_hash(tmp, hash);
	mpz_ctomp(c,hash,SHA256_DIGEST_LENGTH);

	/* hashing id*/
	sha256_hash(id, hash_id);
	mpz_ctomp(hid,hash_id,SHA256_DIGEST_LENGTH);

	/* calculate  */
	mpz_powm(T_c, T, c, n);
	mpz_mul(calced, hid, T_c);
	mpz_mod(hid_T_c, calced, n);

	/* judge */
	result = mpz_cmp(s_e,hid_T_c);

	mpz_clear(s_e);
	mpz_clear(T_c);
	mpz_clear(hid);
	mpz_clear(calced);
	mpz_clear(c);
	mpz_clear(hid_T_c);

	free(tmp);
	return result;

}

int
main(int argc, char *argv[])
{
	unsigned int  i;
	char* text = "hogehoge";
	unsigned char *data;
	unsigned int  dataLen, tmpLen;

	unsigned char hash[SHA256_DIGEST_LENGTH];

	mpz_t p, q, d, n, e;
	mpz_t c, m, mm;
	mpz_t x;
	mpz_t T,s;
	int pb, qb, eb;
	char* id;
	int b;
	clock_t gen_start, gen_end, gen_tmp, verif_start, verif_end, verif_tmp;

	data = (unsigned char *) text;
	dataLen =(unsigned int)strlen(text);
	id = "1234";

	gen_tmp = 0;
	verif_tmp = 0;

	printf("Testing Shamir's IBS scheme(Sh-IBS)\n");

	printf("RSA n key Length (bits) : %d\n", RSA_N_LEN);

	for(int i=1; i<=LOOP_N; i++){

		printf("*************************************[[[%d times]]]*************************************\n",i);
		mpz_init(p);
		mpz_init(q);
		mpz_init(d);
		mpz_init(n);
		mpz_init(e);

		setup(p, q, n, d, e, pb, qb, eb);

		printf("p = "); mpz_out_str(stdout, 16, p); puts("");
		printf("q = "); mpz_out_str(stdout, 16, q); puts("");
		printf("n = "); mpz_out_str(stdout, 16, n); puts("");
		printf("e = "); mpz_out_str(stdout, 16, e); puts("");
		printf("d = "); mpz_out_str(stdout, 16, d); puts("");

		/* Key Derivation*/
		mpz_init(x);
		key_derivation(x,n,e,d,id);

		printf("x = "); mpz_out_str(stdout, 16, x); puts("");

		mpz_init(T);
		mpz_init(s);

		/* signature generation */
		gen_start = clock();
		signature_generation(T, s, n, e, x, data, dataLen);
		gen_end = clock();
		gen_tmp += gen_end - gen_start;

		/* signature verification */
		verif_start = clock();
		b = signature_verification(n,e,d,id,data,dataLen,T,s);
		verif_end = clock();
		verif_tmp += verif_end - verif_start;

	}

	printf("signature generation : %f[msec]\n", ((double)gen_tmp/LOOP_N));

	printf("signature verification : %f[msec]\n", ((double)verif_tmp/LOOP_N));

	mpz_clear(p);
	mpz_clear(q);
	mpz_clear(d);
	mpz_clear(n);
	mpz_clear(e);
	mpz_clear(x);
	
	return 0;
}

