# -*- coding: utf8 -*-
#Sage Michaels
#Final Project: RSA
#Using the miller-rabin test to find large primes
#Then Eurler's Rule to create a public key encryption system


import string
#Fast modular exponentiation algorithm
#finds (d^e)%f
def fast_mod_exp(d,e,f): #recursive function
    if e==0: #if exponent is 0
        return 1 
    if e%2==1: #if exponent is odd
        if f==None:
            val = fast_mod_exp(d,(e-1),f)
            return val*d
        else:
            val = fast_mod_exp(d%f,(e-1)%f,f)
            return val*d%f
    else: #if exponent is even
        if f == None:
            val = fast_mod_exp(d,(e//2),f)
            return (val*val)
        else:
            val = fast_mod_exp(d,(e//2)%f,f)
            return (val*val)%f

#See if n is a fermat psudo-prime for 2,3, and 5
def is_fermat_psudoprime(n):
	check2 = fast_mod_exp(2,n,n)
	check3 = fast_mod_exp(3,n,n)
	check5 = fast_mod_exp(5,n,n)
	if check2==2 and check3==3 and check5==5:
		return True
	else:
		return False
"""
The following 2 functions are used to create
a list of the first 20 primes p by checking if
any i less than root(p) divides p.
"""
def is_prime(n):
	b = 2
	while b*b<n:
		if n%b == 0:
		    return False
		else:
		    b = b + 1
	return True

def find_first_x_primes(x):
	n = 2
	primes = []
	while x>0:
		if is_prime(n):
			primes = primes + [n]
			n = n +1
			x = x - 1
		else:
			n = n +1
	return primes

first_twenty_primes = find_first_x_primes(20)

""" miller_rabin_func runs the miller_rabin_test
on the first 20 primes and returns true if each
test returns "probably prime" and false if any prime
prime tests lead to a "definitely composite".
"""

def miller_rabin_func(n):
	s = 0
	m = n - 1
	while m%2==0:
		s = s + 1
		m = m//2
	prime_tests = first_twenty_primes
	i = 0
	while i<len(prime_tests):
	    b = prime_tests[i]
	    if miller_rabin_test(n,b,s,m):
	    	i = i + 1
	    else:
	    	return False
	return True

def miller_rabin_test(n,b,s,m):
	b = fast_mod_exp(b,m,n)
	if b == 1:
		return True
	while s>0:
		if b == n-1:
			return True
		b = (b*b) % n
		s = s-1
	if b == n - 1:
		return True
	else:
		return False
"""
The following combines the 3 tests described above
to detirmine if a given n is probably prime

First it checks if n is divisable by the first 20 primes
then checks if its a Fermat psudo-prime
then preforms the miller rabin test

This ordering is intentional since it's better to
do the easier computations first as to not
waste time with the harder ones when possible.


"""
def strong_psudo_prime_test(n):
	i = 0 
	while i < len(first_twenty_primes):
		if n%first_twenty_primes[i]==0:
			if n==first_twenty_primes[i]:
				print("in first 20 primes")
				return True
			return False
		else:
			i = i + 1
	if is_fermat_psudoprime(n): 
		print("is a Fermat psudoprime\n")
		if miller_rabin_func(n): 
			print("Passed Miller Rabin\n")
			print("is a strong psudoprime\n")
			return True 
		else:
			print("failed miller-rabin test\n")
			return False
	else:
		print("not a fermat psudoprime\n")
		return False



def find_candidate_prime(n):
	i = 1
	while i>0:
		candidate = 2*n+i
		print("checking" + str(candidate) + "...\n")
		if strong_psudo_prime_test(candidate):
			print("Passed")
			return candidate
		else:
			print("failed.")
			i = i + 2
	print("try another n")


import random

"""
The following uses the Lucas–Pocklington–Lehmer Criterion 
to generate guaranteed primes longer than a specified number
of digits.

"""

def gcd(x,y):
	if y==0:
		return x
	else:
		x = x%y
		return gcd(y,x)


def num_of_digits(x):
	i = 0
	while x>0:
		i = i + 1
		x = x//10
	return i

def meets_lplc(n,u):
	test1 = (fast_mod_exp(2,(n-1),n) == 1)
	test2 = (gcd(fast_mod_exp(2,u,n)+n-1,n) == 1)
	if test1 and test2:
		return True
	else:
		return False

"""
lpl_prime repeatedly finds larger and larger
lpl primes until it generates one with more than
the specified number of digits.

meets_lplc checks that the generated lpl_prime meets the
Lucas–Pocklington–Lehmer Criterion.

"""

def lpl_prime(digits): 
	p = 1000003
	digit_count = 7
	while digit_count < digits:
		random.seed()
		u = random.randint(1,p//2)
		u = u*2
		not_prime = True
		while not_prime and u<p:
			candidate = u*p + 1
			not_prime = not(meets_lplc(candidate,u))
			if not_prime:
				u = u + 2
		p = candidate
		digit_count = num_of_digits(candidate)
	return p
"""
The following ext_gcd function is used to find the inverse of the 
encryption key mod totient(n), where 'n' is a composite number composed
of two large primes.

Since ext_gcd will be called on a number 'b' coprime to the totient of 'n' and 
the totient of 'n', ext_gcd will gives back the number 'a' such that 
(totient n)*d + b*a = gcd(totient n,b)=1 =a*b mod (totient n).

"""
#a = totient(n), b = public key
def ext_gcd(a,b):
	def helper(a,b,w,x,y,z):
		if b == 0:
			return (x)
		else:
			t = w-(a//b)*y
			s = x-(a//b)*z
			return helper(b,a%b,y,z,t,s) 
	return helper(a,b,1,0,0,1)


def make_encryption_keys(n_digit):
	p = lpl_prime(n_digit//2) #first prime "p"
	q = lpl_prime(n_digit//2) #second prime "q"
	while p==q: 
		q = lpl_prime(n_digit//3)
	n = p*q #our large composite number
	n_totient = (p-1)*(q-1) #since phi(n)=phi(pq)=phi(p)*phi(q)=(p-1)*(q-1)
	random.seed()
	d = random.randint(1,n_totient) #potential public key
	while gcd(n_totient,d)!=1 or gcd(p,d)!=1 or gcd(q,d)!=1:
		d = random.randint(1,n_totient)
	e = ext_gcd(n_totient,d) #private key since 1=d^(n_totient)= d*d^(n_totient - 1)=d*d_inverse
	f = e%n_totient
	print("PUBLIC: composite number n is : " +str(n) + "\n")
	print("PUBLIC: encryption key is: " + str(d) + "\n")
	print("PRIVATE: decryption key is: " + str(f) + "\n")
	return(n,d,f)

#creates table for converting letters, spaces, and "." to 2-digit integers.

encoder = dict()
for index, letter in enumerate(string.ascii_lowercase): #assigned integer value to lowercase, uppercase, and punctuation characters
    encoder[letter] = index + 10
encoder[" "] = 36

decoder = dict() #dictionary that swaps keys and values of encoder
for letter in encoder:
	p_text = encoder[letter]
	decoder[p_text] = letter


def encode(message):
    plaintext = []
    coded = []
    i = 0
    while i<len(message):
    	coded.append(str(encoder[message[i]])) #converts each letter to an int in string form
    	i = i + 1
    while (len(coded))%3!=0: #adds blank spaces to end
    	coded.append(str(encoder[" "])) #so all blocks contain 3 characters
    i = 0
    j = 0
    while i+2<len(coded): #concatinates 3 integer values from converted message into one entry
    	plaintext.append(int(coded[i]+coded[i+1]+coded[i+2]))
    	j = j + 1
    	i = i + 3
    print("plaintext:")
    print(plaintext)
    return plaintext

def decode(plaintext):
	decoded = ""
	p_text = []
	i = 0
	while i<len(plaintext):
		three_char = str(plaintext[i])
		j = 0
		while j < 6:
			p_text.append(int(three_char[j:j+2]))
			j = j + 2
		i = i + 1
	i = 0
	while i<len(p_text):
		decoded = decoded + decoder[p_text[i]]
		i = i + 1
	return decoded


def message_encrypter(message, n ,public_key):
	unencrypted = encode(message)
	encrypted = []
	i = 0
	while i < len(unencrypted): #encrypts each portion of encoded message
		encrypted.append(fast_mod_exp(unencrypted[i],public_key,n))
		i = i + 1
	encrypted
	print("message encrypted...")
	return encrypted

def message_decrypter(private_key, n, encrypted):
	print("message decrypting...")
	i = 0
	decrypted = []
	while i < len(encrypted):
		d = encrypted[i]
		b = fast_mod_exp(d,private_key,n)
		decrypted.append(b)
		i = i + 1
	message = decode(decrypted)
	print("message decrypted.")
	return message

 
def make_encrypter_decrypter_functions(n,public_key,private_key):
	def helper_1(x):
		return message_encrypter(x,n,public_key)
	def helper_2(ys):
		return message_decrypter(private_key,n,ys)
	return (helper_1,helper_2)

#n , public, private
(n,d,f) = make_encryption_keys(100)

#functions for encrypting and decrypting messages
#"encrypt" takes a string "decrypt" takes a list of encrypted
#characters, encrypt can be shared publicly, decrypt must stay secret.
(encrypt,decrypt) = make_encrypter_decrypter_functions(n,d,f)
print("use function: encrypt(\"message\")\n NOTE: encrypt can only handle lower case letters and spaces")
print("use function: decrypt(encrypted message) to decrypt \n")


print("d = encrypt(\"this is how you encrypt a message\")")
d = encrypt("this is how you encrypt a message")
print("d = " + str(d))
print("c = decrypt(d)")
c = decrypt(d)
print('c =' + str(c))


"""
Bibliography

Coutinho, S. C. The Mathematics of Ciphers: Number Theory and RSA Cryptography.
Natick, MA: K Peters, 1999. Print.


Pommersheim, James E., Tim K. Marks, and Erica Flapan.
Number Theory: A Lively Introduction with Proofs, Applications, and Stories.
Hoboken, NJ: Wiley, 2010. Print.

"""




