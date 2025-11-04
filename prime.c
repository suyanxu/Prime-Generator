#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <string.h>
const int pNum = 32;
const int N = 32, maxSize = 70;
const unsigned long long p = 1ll << 32ll;
struct Bignum
{
    int n, sign;
    unsigned long long num[70]; // 1-indexed
} const0, const1, const2, rubbish;
const unsigned long long numsize = sizeof(struct Bignum);
int cmp(struct Bignum *num1, const char op, struct Bignum *num2);
void init(struct Bignum *num1, unsigned long long number);
unsigned maxNum(unsigned a, unsigned b)
{
    return (a > b) ? a : b;
}
void autoSetn(struct Bignum *bignum)
{
    for (int i = maxSize - 1; i >= 1; i--)
    {
        if (bignum->num[i] != 0)
        {
            bignum->n = i;
            return;
        }
    }
    bignum->n = 0;
    return;
}
void add(struct Bignum *ans, const struct Bignum *a, const struct Bignum *b)
{
    struct Bignum num1, num2, tempans;
    memcpy(&num1, a, numsize);
    memcpy(&num2, b, numsize);
    memset(&tempans, 0, numsize);
    unsigned long long overflow = 0;
    int n = maxNum(a->n, b->n);
    for (int i = 1; i <= n + 1; i++)
    {
        tempans.num[i] = num1.num[i] + num2.num[i] + overflow;
        overflow = tempans.num[i] >> pNum;
        tempans.num[i] -= overflow << pNum;
    }
    if (overflow == 1)
    {
        tempans.n = n + 1;
    }
    else
    {
        tempans.n = n;
    }
    memcpy(ans, &tempans, numsize);
    return;
}
void sub(struct Bignum *ans, struct Bignum *a, struct Bignum *b)
{
    struct Bignum num1, num2, tempans;
    memcpy(&num1, a, numsize);
    memcpy(&num2, b, numsize);
    memset(&tempans, 0, numsize);
    if (cmp(b, '>', a))
    {
        tempans.sign = -1;
        memcpy(&num1, b, numsize);
        memcpy(&num2, a, numsize);
    }
    unsigned long long overflow = 0;
    int n = num1.n;
    for (int i = 1; i <= n; i++)
    {
        long long temp = num1.num[i] - num2.num[i] - overflow;
        if (temp < 0)
        {
            temp += p;
            overflow = 1;
        }
        else
        {
            overflow = 0;
        }
        tempans.num[i] = temp;
    }
    int cnt = num1.n;
    for (; cnt >= 1; cnt--)
    {
        if (!!tempans.num[cnt])
        {
            break;
        }
    }
    tempans.n = cnt;
    memcpy(ans, &tempans, numsize);
    return;
}
void mul(struct Bignum *ans, const struct Bignum *a, const struct Bignum *b)
{
    struct Bignum num1, num2, tempans;
    memcpy(&num1, a, numsize);
    memcpy(&num2, b, numsize);
    memset(&tempans, 0, numsize);
    unsigned long long overflow = 0;
    for (int i = 1; i <= num1.n; i++)
    {
        for (int j = 1; j <= num2.n; j++)
        {
            tempans.num[i + j - 1] += num1.num[i] * num2.num[j];
            overflow = tempans.num[i + j - 1] >> pNum;
            tempans.num[i + j - 1] -= overflow << pNum;
            tempans.num[i + j] += overflow;
        }
    }
    if (overflow)
    {
        tempans.n = num1.n + num2.n;
    }
    else
    {
        tempans.n = num1.n + num2.n - 1;
    }
    memcpy(ans, &tempans, numsize);
    return;
}
void leftshuffle(struct Bignum *bignum, int cnt)
{
    for (int i = bignum->n + cnt; i >= (cnt + 1); i--)
    {
        bignum->num[i] = bignum->num[i - cnt];
    }
    for (int i = 1; i <= cnt; i++)
    {
        bignum->num[i] = 0;
    }
    autoSetn(bignum);
}
void Bigdiv2(struct Bignum *ans, struct Bignum *r, struct Bignum *a)
{
    struct Bignum tempans;
    memcpy(&tempans, a, numsize);
    unsigned long long last = 0;
    for (int i = tempans.n; i >= 1; i--)
    {
        unsigned long long temp = tempans.num[i] & 1;
        tempans.num[i] >>= 1;
        tempans.num[i] |= (last << (pNum - 1));
        last = temp;
    }
    autoSetn(&tempans);
    memcpy(ans, &tempans, numsize);
    init(r, last);
    return;
}
void Bigdiv(struct Bignum *ans, struct Bignum *r, struct Bignum *a, struct Bignum *b)
{
    struct Bignum num1, num2, tempans, tempr, temp, temp1, temp2;
    memcpy(&num1, a, numsize);
    memcpy(&num2, b, numsize);
    memset(&tempans, 0, numsize);
    memset(&tempr, 0, numsize);
    if (cmp(&num2, '>', &num1))
    {
        memcpy(r, a, numsize);
        memset(ans, 0, numsize);
        return;
    }
    for (int i = num1.n - num2.n; i >= 0; i--)
    {
        long long left = 0, right = p, mid;
        while (1)
        {
            mid = (left + right) / 2;
            memset(&temp, 0, numsize);
            temp.n = 1;
            temp.num[1] = mid;
            memcpy(&temp1, &num1, numsize);
            memcpy(&temp2, &num2, numsize);
            mul(&temp2, &temp2, &temp);
            leftshuffle(&temp2, i);
            if (cmp(&temp1, '<', &temp2))
            {
                right = mid - 1;
            }
            else
            {
                left = mid + 1;
            }
            if (right < left)
            {
                break;
            }
        }
        mid = (left + right) / 2;
        temp.n = 1;
        temp.num[1] = mid;
        memcpy(&temp2, &num2, numsize);
        mul(&temp2, &temp2, &temp);
        leftshuffle(&temp2, i);
        sub(&num1, &num1, &temp2);
        tempans.num[i + 1] = mid;
    }
    memcpy(ans, &tempans, numsize);
    memcpy(r, &num1, numsize);
    autoSetn(ans);
    autoSetn(r);
    // printtime();
    return;
}
void printNum(const struct Bignum *bignum, FILE *fp)
{
    if (bignum->sign == -1)
    {
        fprintf(fp, "-");
    }
    fprintf(fp, "%llx", bignum->num[bignum->n]);
    for (int i = bignum->n - 1; i >= 1; i--)
    {
        fprintf(fp, "%08llx", bignum->num[i]);
    }
}
int hex2dec(char c)
{
    if (c >= '0' && c <= '9')
    {
        return c - '0';
    }
    return c - 'a' + 10;
}
void readNum(struct Bignum *bignum)
{
    char s[100];
    memset(s, 0, sizeof(s));
    scanf("%s", s);
    int lens = strlen(s);
    int cnt = lens - 1, pos = 0;
    while (1)
    {
        if (cnt <= 2)
        {
            break;
        }
        int temp = (hex2dec(s[cnt])) | (hex2dec(s[cnt - 1]) << 4) | (hex2dec(s[cnt - 2]) << 8) | (hex2dec(s[cnt - 3]) << 12);
        pos++;
        bignum->num[pos] = temp;
        cnt -= 4;
    }
    int temp = 0;
    switch (cnt)
    {
    case 2:
        temp = (hex2dec(s[0]) << 8) | (hex2dec(s[1]) << 4) | (hex2dec(s[2]));
        break;
    case 1:
        temp = (hex2dec(s[0]) << 4) | (hex2dec(s[1]));
        break;
    case 0:
        temp = (hex2dec(s[0]));
        break;
    case -1:
        temp = 0;
        break;
    default:
        break;
    }
    if (cnt != -1)
    {
        bignum->n = pos + 1;
        bignum->num[pos + 1] = temp;
    }
    else
    {
        bignum->n = pos;
    }
    bignum->sign = 1;
    return;
}
int cmp(struct Bignum *num1, const char op, struct Bignum *num2)
{
    struct Bignum *a = num1;
    struct Bignum *b = num2;
    struct Bignum *temp = NULL;
    switch (op)
    {
    case '=':
        if (a->n != b->n)
        {
            return 0;
        }
        for (int i = a->n; i >= 1; i--)
        {
            if (a->num[i] != b->num[i])
            {
                return 0;
            }
        }
        return 1;
        break;
    case '<':
        temp = b;
        b = a;
        a = temp;
    case '>':
        if (a->n > b->n)
        {
            return 1;
        }
        else if (a->n < b->n)
        {
            return 0;
        }
        for (int i = a->n; i >= 1; i--)
        {
            if (a->num[i] < b->num[i])
            {
                return 0;
            }
            else if (a->num[i] > b->num[i])
            {
                return 1;
            }
        }
        return 0;
        break;
    default:
        return -1;
        break;
    }
}
void Bigpow(struct Bignum *ans, struct Bignum *num1, struct Bignum *power)
{
    struct Bignum tempans;
    init(&tempans, 1);
    struct Bignum temp, temppower;
    memcpy(&temp, num1, numsize);
    memcpy(&temppower, power, numsize);
    while (!cmp(&temppower, '=', &const0))
    {
        if (temppower.num[1] & 1)
        {
            mul(&tempans, &tempans, &temp);
        }
        mul(&temp, &temp, &temp);
        Bigdiv2(&temppower, &rubbish, &temppower);
    }
    memcpy(ans, &tempans, numsize);
    return;
}
void Bigpowmod(struct Bignum *ans, struct Bignum *num1, struct Bignum *power, struct Bignum *mod)
{
    struct Bignum temp, temppower, tempans;
    init(&tempans, 1);
    memcpy(&temp, num1, numsize);
    memcpy(&temppower, power, numsize);
    while (temppower.n)
    {
        if (temppower.num[1] & 1)
        {
            mul(&tempans, &tempans, &temp);
            struct Bignum az;
            init(&az, 1ull);
            Bigdiv(&rubbish, &tempans, &tempans, mod);
        }
        mul(&temp, &temp, &temp);
        Bigdiv(&rubbish, &temp, &temp, mod);
        Bigdiv2(&temppower, &rubbish, &temppower);
    }
    memcpy(ans, &tempans, numsize);
    return;
}
void init(struct Bignum *num1, unsigned long long number)
{
    memset(num1, 0, numsize);
    if (number < p)
    {
        if (number == 0)
        {
            return;
        }
        num1->n = 1;
        num1->num[1] = number;
        return;
    }
    num1->n = 2;
    num1->num[1] = number & 0xffffffffull;
    num1->num[2] = (number & 0xffffffff00000000ull) >> pNum;
    return;
}
void random_generate_prime(struct Bignum *num)
{
    memset(num, 0, numsize);
    num->n = N;
    for (int i = 1; i <= N; i++)
    {
        num->num[i] = (((unsigned long long)rand()));
        num->num[i] <<= 15;
        num->num[i] += (((unsigned long long)rand()));
    }
    num->num[N] |= 0x80000000ll;
    num->num[1] |= 1ll;
    return;
}
void random_generate_number(struct Bignum *num, int length)
{
    memset(num, 0, numsize);
    num->n = length;
    for (int i = 1; i <= length; i++)
    {
        num->num[i] = (rand()) & 0xffffll + ((rand()) & 0xffffll) << 15ll;
    }
    num->num[length] |= 0x80000000ll;
    return;
}
int isPrime(struct Bignum *testnum, struct Bignum *num1)
{
    struct Bignum tempnum;
    memcpy(&tempnum, num1, numsize);
    sub(&tempnum, &tempnum, &const1);
    int cnt0 = 0;
    for (int i = 1; i <= tempnum.n; i++)
    {
        if (tempnum.num[i] == 0)
        {
            cnt0 += pNum;
        }
        else
        {
            unsigned long long tmp = tempnum.num[i];
            while (!(tmp & 1))
            {
                tmp >>= 1;
                cnt0++;
            }
            break;
        }
    }
    struct Bignum temp2, q, a, k;
    init(&k, (unsigned long long)cnt0);
    Bigpow(&temp2, &const2, &k);
    Bigdiv(&q, &rubbish, &tempnum, &temp2);
    memcpy(&a, testnum, numsize);
    Bigpowmod(&temp2, &a, &q, num1);
    if (cmp(&temp2, '=', &const1))
    {
        return 1;
    }
    if (cmp(&temp2, '=', &tempnum))
    {
        return 1;
    }
    for (int i = 1; i <= cnt0 - 1; i++)
    {
        Bigpowmod(&temp2, &temp2, &const2, num1);
        if (cmp(&temp2, '=', &tempnum))
        {
            return 1;
        }
    }
    return 0;
}
int Miller_Rabin(struct Bignum *num1)
{
    const int TEST_NUM = 10;
    for (int i = 1; i <= TEST_NUM; i++)
    {
        struct Bignum testnum;
        random_generate_number(&testnum, num1->n);
        if (!isPrime(&testnum, num1))
        {
            return 0;
        }
    }
    return 1;
}
struct Bignum ans1, ans2, num1, num2, num3;
const int MAX_PRIME = 1000;
char prime[1234];
int primelist[1234], primecount;
int main()
{
    FILE *fp = fopen("prime.txt", "w");
    for (int i = 2; i <= MAX_PRIME; i++)
    {
        prime[i] = 1;
    }
    for (int i = 2; i <= MAX_PRIME; i++)
    {
        if (prime[i])
        {
            for (int j = i * i; j <= MAX_PRIME; j += i)
            {
                prime[j] = 0;
            }
        }
    }
    for (int i = 2; i <= MAX_PRIME; i++)
    {
        if (prime[i])
        {
            primelist[++primecount] = i;
        }
    }
    init(&const0, 0ull);
    init(&const1, 1ull);
    init(&const2, 2ull);
    srand(time(NULL));
    for (int i = 1; i <= 10; i++)
    {
        random_generate_prime(&num1);
        printf("Number %d:\n", i);
        printNum(&num1, stdout);
        int ret = Miller_Rabin(&num1);
        printf("\n%s\n", ret ? "prime" : "Composite");
    }
    printf("Now start generating prime:\n");
    clock_t starttime = clock();
    while (1)
    {
    generate:
        random_generate_prime(&num1);
        struct Bignum temp;
        for (int i = 1; i <= primecount; i++)
        {
            init(&temp, (unsigned long long)primelist[i]);
            Bigdiv(&rubbish, &temp, &num1, &temp);
            if (cmp(&temp, '=', &const0))
            {
                goto generate;
            }
        }
        int flag = Miller_Rabin(&num1);
        if (flag)
        {
            printf("Time used:%.3f sec\n", ((double)(clock() - starttime)) / CLOCKS_PER_SEC);
            printNum(&num1, stdout);
            printf("\n");
            printNum(&num1, fp);
            fclose(fp);
            system("pause");
            return 0;
        }
    }
    return 0;
}