import numpy as np
import time
import sys
import datetime
import os
from scipy.sparse import csr_matrix
import re
import random
import hmac
import hashlib
import pickle
import gmpy
import gmpy2
from gmpy2 import mpz
from Crypto.Cipher import AES
from Crypto.Util.Padding import pad, unpad
from pypbc import *
import json
import string
import binascii
import json
from web3.middleware import geth_poa_middleware
import struct
from web3 import Web3, HTTPProvider, IPCProvider, WebsocketProvider
from hexbytes import  HexBytes

BLOCK_SIZE = 16  # bytes
random_length = 128
debug = False
sys.setrecursionlimit(10000)
w3 = Web3(Web3.HTTPProvider("http://127.0.0.1:8540"))
w3.middleware_onion.inject(geth_poa_middleware, layer=0)
# read kw-file
f_Kw_File_Use = open('/home/mwang235/Dropbox/Code/DataSharing/Kw_File_Use.txt', 'rb')
Kw_File_Use = pickle.load(f_Kw_File_Use)

kw_prime_file = {}


# map kw to primes
def kw_to_primes(kw_prime):
    print("generate kw to prime file")
    prime = 2
    for kw in Kw_File_Use:
        prime = gmpy2.next_prime(prime)
        kw_prime[kw] = prime
    return 0


# pypbc
# Element Pairing Parameters
def setup():
    """
    Generates public key and master secret key.
    :return:
    """
    if debug:
        print('\nSetup algorithm:\n')

    params = Parameters(qbits=512, rbits=160)  # type a
    pairing = Pairing(params)
    # G2 generator g
    g = Element.random(pairing, G2)  # 1024 bytes
    # x y
    x_ran = Element.random(pairing, Zr)  # 160 bits
    y_ran = Element.random(pairing, Zr)

    # define global attributes
    attr_list = ['ONE', 'TWO', 'THREE']
    attr_value = [['A', 'B', 'C'], ['D', 'E'], ['F', 'G', 'H']]

    # compute X, Y
    X = {}
    Y = {}
    PB = Element(pairing, GT)
    PB = pairing.apply(g, g)
    for i in range(len(attr_list)):
        # list_X_i = []
        # list_Y_i = []
        for k_i in range(len(attr_value[i])):
            # print(len(attr_value[attr_list[i]]))
            # print(k_i)
            # string concatenation and to bytes
            cat_x = str(i) + str(k_i) + str(x_ran)
            # print(len(cat_x))
            # H0
            hash_value_x = Element.from_hash(pairing, Zr, cat_x)
            # print('test', hash_value_x)
            # Xi
            X_i_k = Element(pairing, G2, value=g ** -hash_value_x)
            X.setdefault(i,[]).append(X_i_k)
            # list_X_i.append(X_i_k)
            cat_y = str(i) + str(k_i) + str(y_ran)
            hash_value_y = Element.from_hash(pairing, Zr, cat_y)
            # bilinear pairing
            Y_i_k = Element(pairing, GT, value=PB ** hash_value_y)
            Y.setdefault(i, []).append(Y_i_k)
            # list_Y_i.append(Y_i_k)
        # X[i] = list_X_i
        # Y[i] = list_Y_i

    # the public key
    pk = {'pairing': pairing, 'g': g, 'X': X, 'Y': Y}
    # print('public key')
    # print(g)
    # print(X)
    # print(Y)

    # the master key
    msk = {'x': x_ran, 'y': y_ran}
    # print('master key')
    # print(x_ran, y_ran)

    return pk, msk


def keygen(pk, msk):
    """
    Generate a key for a user with a list of attributes.
    :param pk:
    :param msk:
    :param attr_L:
    :return:
    """

    if debug:
        print('\nKey generation algorithm:\n')

    g = pk['g']
    pairing = pk['pairing']
    x = msk['x']
    y = msk['y']
    # attr_L example
    # attribute: 'ONE': 'A', 'B', 'THREE': 'H'
    attr_L = {0: [0, 1], 2: [2]}

    # random sk
    # params = Parameters(qbits=512, rbits=160)  # type a
    # pairing = Pairing(params)
    sk = Element.random(pairing, Zr)
    # H1
    hash_value_sk = Element.from_hash(pairing, G2, str(sk))
    # sigma
    sigma_key = {}
    for i in attr_L:
        list_sigma = []
        for k_i in range(len(attr_L[i])):
            # print(attr_L[i][k_i])
            cat_i_y = str(i) + str(attr_L[i][k_i]) + str(y)
            hash_value_i_y = Element.from_hash(pairing, Zr, cat_i_y)
            sigma_i_y = Element(pairing, G2, value=g ** hash_value_i_y)
            cat_i_x = str(i) + str(attr_L[i][k_i]) + str(x)
            hash_value_i_x = Element.from_hash(pairing, Zr, cat_i_x)
            sigma_i_x = Element(pairing, G2, value=hash_value_sk ** hash_value_i_x)
            sigma_i_k = Element(pairing, G2, value=sigma_i_y * sigma_i_x)
            list_sigma.append(sigma_i_k)
        sigma_key[i] = list_sigma

    # attribute secret key
    SK_L = {'sk': sk, 'sigma_key': sigma_key}
    # print('secret key')
    # print('sk', sk)
    # print(sigma_key)

    return SK_L


def encrypt(pk, M):
    """
    Encrypt a message under a policy.
    :param pk:
    :param M:
    :return:
    """

    if debug:
        print('\nEncryption Algorithm\n')

    policy_W = {0: [0, 1], 2: [2]}
    g = pk['g']
    pairing = pk['pairing']
    X = pk['X']
    Y = pk['Y']
    # random s
    # params = Parameters(qbits=512, rbits=160)  # type a
    # pairing = Pairing(params)
    s = Element.random(pairing, Zr)

    # subsequent multiply
    X_W = Element.one(pairing, G2)
    Y_W = Element.one(pairing, GT)
    for i in policy_W:
        list_X_i = X.get(i)
        list_Y_i = Y.get(i)
        for j in range(len(policy_W[i])):
            k_i = policy_W[i][j]
            X_W = Element(pairing, G2, value=X_W * list_X_i[k_i])
            Y_W = Element(pairing, GT, value=Y_W * list_Y_i[k_i])

    Y_W_s = Element(pairing, GT, value=Y_W ** s)
    C_0 = Element(pairing, GT, value=M * Y_W_s)
    C_1 = Element(pairing, G2, value=g ** s)
    C_2 = Element(pairing, G2, value=X_W ** s)
    # print(C_0)
    # print(C_1)
    # print(C_2)

    CT_W = {'policy': policy_W, 'C_0': C_0, 'C_1': C_1, 'C_2': C_2}

    return CT_W


def decrypt(pk, CT_W, SK_L):
    """
    Decrypt ciphertext with key.
    :param pk:
    :param CT_W:
    :param SK_L:
    :return:
    """
    if debug:
        print('\nDecryption Algorithm\n')

    # params = Parameters(qbits=512, rbits=160)  # type a
    # pairing = Pairing(params)
    pairing = pk['pairing']
    sk = SK_L['sk']
    hash_value_sk = Element.from_hash(pairing, G2, str(sk))
    sigma_key = SK_L['sigma_key']
    policy_W = CT_W['policy']
    C_0 = CT_W['C_0']
    C_1 = CT_W['C_1']
    C_2 = CT_W['C_2']

    sigma_W = Element.one(pairing, G2)
    for i in sigma_key:
        list_sigma_key = sigma_key[i]
        for j in range(len(sigma_key[i])):
            sigma_W = Element(pairing, G2, value=sigma_W * list_sigma_key[j])
    sigma_C_1 = Element(pairing, GT)
    sigma_C_1 = pairing.apply(sigma_W, C_1)
    sk_C_2 = Element(pairing, GT)
    sk_C_2 = pairing.apply(hash_value_sk, C_2)
    sigma_C_1_2 = Element(pairing, GT, value=sigma_C_1 * sk_C_2)
    M = Element(pairing, GT, value=C_0 * (sigma_C_1_2 ** (-1)))
    print('dec_M', M)

    return M


# generate random string
def random_string(random_string_length):
    seed = "01"
    sa = []
    for i in range(random_string_length):
        sa.append(random.choice(seed))
    salt = ''.join(sa)
    salt_hex = hex(int(salt, 2))
    return salt_hex


g1 = mpz(2141434891434191460597654106285009794456474073127443963580690795002163321265105245635441519012876162226508712450114295048769820153232319693432987768769296824615642594321423205772115298200265241761445943720948512138315849294187201773718640619332629679913150151901308086084524597187791163240081868198195818488147354220506153752944012718951076418307414874651394412052849270568833194858516693284043743223341262442918629683831581139666162694560502910458729378169695954926627903314499763149304778624042360661276996520665523643147485282255746183568795735922844808611657078638768875848574571957417538833410931039120067791054495394347033677995566734192953459076978334017849678648355479176605169830149977904762004245805443987117373895433551186090322663122981978369728727863969397652199851244115246624405814648225543311628517631088342627783146899971864519981709070067428217313779897722021674599747260345113463261690421765416396528871227)
p = mpz(3268470001596555685058361448517594259852327289373621024658735136696086397532371469771539343923030165357102680953673099920140531685895962914337283929936606946054169620100988870978124749211273448893822273457310556591818639255714375162549119727203843057453108725240320611822327564102565670538516259921126103868685909602654213513456013263604608261355992328266121535954955860230896921190144484094504405550995009524584190435021785232142953886543340776477964177437292693777245368918022174701350793004000567940200059239843923046609830997768443610635397652600287237380936753914127667182396037677536643969081476599565572030244212618673244188481261912792928641006121759661066004079860474019965998840960514950091456436975501582488835454404626979061889799215263467208398224888341946121760934377719355124007835365528307011851448463147156027381826788422151698720245080057213877012399103133913857496236799905578345362183817511242131464964979)
q = mpz(93911948940456861795388745207400704369329482570245279608597521715921884786973)  # 阶

# g1_b = str.encode(str(g1))
# print(len(g1_b))

# generate all keys
secret_k = hmac.new(b'secretk', digestmod='MD5').digest()
# print('secretkey',secret_k)
master_K_I = hmac.new(b'masterKI', digestmod='MD5').digest()
master_K_Z = hmac.new(b'masterKZ', digestmod='MD5').digest()
master_K_X = hmac.new(b'masterKX', digestmod='MD5').digest()


# str不是16的倍数那就补足为16的倍数
# def add_to_16(value):
#     while len(value) % 16 != 0:
#         value += '\0'
#     return str.encode(value)  # 返回bytes


# transform id to points in GT
def file_id_GT(pk, id):
    id_GT = {}
    pairing = pk['pairing']
    g = pk['g']
    M = Element(pairing, GT)
    M = pairing.apply(g, g)
    s = random.randint(10, 1000)
    M = Element(pairing, GT, value=M ** s)
    id_GT[id] = M
    # print(id_GT)
    return id_GT
# def x_o_r(byte1, byte2):
#     xor_cipher = []
#     for j in range(random_length):
#         xor_cipher.append(byte1[j] ^ byte2[j])
#     cipher = ''.join(str(i) for i in xor_cipher)
#     return str.encode(cipher)  # bytes


def localPad(data_hex):  # no 0x
    # b = data_hex[2:]
    return "0x" + '0' * (64 - len(data_hex[2:])) + data_hex[2:]


# 为所有关键字所有文件生成index
def build_index(pk, Kw_File, kw_prime):
    print('---------------------------------------Build Index')
    CEDB = {}  # on chain encrypted database
    CPT = {}  # on chain partial token
    CBSIndex = []
    # print(CEDB, CBSIndex, CPT)
    for w in kw_prime:  # 需要先生成kw_prime_file，将kw与素数的对应关系保存
        c = 0
        st_0 = random_string(random_length)  # str hex
        # print('st_0', type(st_0), len(st_0), st_0)
        st_0_hex = localPad(st_0)
        # print('st_0_hex', type(st_0_hex), len(st_0_hex), st_0_hex)
        st_0_hex_bytes = Web3.toBytes(hexstr=st_0_hex)
        st = {0: st_0_hex_bytes}  # bytes hex  len = 32
        # print('st[0]', type(st[0]), len(st[0]), st[0])
        l_st_c = []
        # stag_w
        inv_w = gmpy2.invert(kw_prime[w], q)
        # stag_w = hmac.new(secret_k, str.encode(str(gmpy2.powmod(g1, mpz(inv_w) % q, p))), digestmod='md5').digest()  # bytes
        # print('stag_w', type(stag_w), len(stag_w), stag_w)
        stag_w_hex = hmac.new(secret_k, str.encode(str(gmpy2.powmod(g1, mpz(inv_w) % q, p))), digestmod='md5').hexdigest()  # str
        # print('stag_w_hex', type(stag_w_hex), len(stag_w_hex), stag_w_hex)
        # stag_w_bytes = Web3.toBytes(hexstr=stag_w_hex)
        # print('stag_w', type(stag_w), len(stag_w), stag_w)
        # CPT 键 l
        l = Web3.keccak(str.encode(stag_w_hex))
        # print('l', len(l), type(l), l)
        for ind in range(len(Kw_File[w])):
            e = []
            c = c + 1
            t_c_ori = random_string(random_length)  # str hex
            # print('t_c_ori', type(t_c_ori), len(t_c_ori), t_c_ori)
            t_c_hex = localPad(t_c_ori)
            t_c = Web3.toBytes(hexstr=t_c_hex)  # bytes hex 32
            # print('t_c', type(t_c), len(t_c), t_c)
            # P AES加密，在search阶段需要解密onchain,t_c是key,st_c-1是M
            # aes_st_c = AES.new(t_c, AES.MODE_ECB)
            # print('st[c-1]', st[c-1])
            # st[c] = aes_st_c.encrypt(pad(st[c-1], BLOCK_SIZE))  # Crypto padding
            st[c] = bytes(a ^ b for a, b in zip(t_c, st[c-1]))  # bytes 32
            # print('st[c]', type(st[c]), len(st[c]), st[c])
            # decrypt
            # test_decrypt = unpad(aes_st_c.decrypt(st[c]), BLOCK_SIZE)
            # print('test_decrypt', test_decrypt)
            # string_c = str(stag_w) + str(st[c])  # string
            # bytes_stagw_c = stag_w_bytes + st[c]  # bytes 48
            # print('bytes_stagw_c', type(bytes_stagw_c), len(bytes_stagw_c), bytes_stagw_c)
            # string_c = Web3.toBytes(hexstr='0x' + stag_w_hex) + Web3.toBytes(hexstr=localPad(Web3.toHex(st[c])))
            string_c = stag_w_hex + localPad(Web3.toHex(st[c]))[2:]
            # bytes_st_c = Web3.toBytes(hexstr=localPad(stag_w_hex)) + st[c]
            # u H1 keccak
            # u = str.encode((Web3.keccak(str.encode(string_c))).hex())
            # u = Web3.keccak(bytes_st_c)
            u_str = (Web3.keccak(hexstr=string_c)).hex()  # blockchain  str 66
            u = Web3.toBytes(hexstr=u_str)
            # u= Web3.keccak(str.encode(str(string_c)))
            # u = str.encode(Web3.keccak(bytes_stagw_c).hex())
            # u = (Web3.keccak(bytes_stagw_c)).hex() # blockchain
            print('u', type(u), len(u), u)  # bytes
            # e = 'ABE.Enc(id)' + '0' + str(t_c) 将e设计为存储5个值的list
            # transform id to GT points
            id_GT_use = file_id_GT(pk, Kw_File[w][ind])
            e_id = encrypt(pk, id_GT_use[Kw_File[w][ind]])
            # print(type(e_id['C_1']))  # 'pypbc.Element'
            e.append(str.encode(str(e_id['C_0'])))
            # e.append(HexBytes(str(e_id['C_0'])))
            e.append(str.encode(str(e_id['C_1'])))
            # e.append(HexBytes(str(e_id['C_1'])))
            e.append(str.encode(str(e_id['C_2'])))
            # e.append(HexBytes(str(e_id['C_2'])))
            delta = 0
            e.append(delta)  # int
            # e.append(str.encode(str(delta)))
            # e.append(HexBytes(str(delta)))
            e.append(t_c)
            # print('e', e)
            # 异或
            # e = bytes(a ^ b for a, b in zip(string_id, sha256.digest()))
            z_w = gmpy2.powmod(g1, mpz(inv_w) % q, p)
            z = hmac.new(master_K_Z, str.encode(str(z_w) + str(c)), digestmod='md5').hexdigest()  # bytes
            # print('z', z, type(z), len(z))
            xind = hmac.new(master_K_I, str.encode(Kw_File[w][ind]), digestmod='md5').hexdigest()  # bytes
            # print('xind', xind, type(xind), len(xind))
            # 此处y是什么数据类型 1.将z限制在群中，直接求逆
            # y = int.from_bytes(xind, byteorder='big') / int.from_bytes(z, byteorder='big')
            zz = int.from_bytes(str.encode(z), byteorder='big', signed=False)
            inv_z = gmpy2.invert(mpz(zz), q)
            y = ((mpz(int.from_bytes(str.encode(xind), byteorder='big',signed=False)) % q) * (mpz(inv_z) % q)) % q
            # y_bytes = str.encode(str(y))  # bytes
            y_bytes = Web3.toBytes(hexstr=hex(int(y)))
            # print('y_bytes', type(y_bytes), len(y_bytes), y_bytes)
            e.append(y_bytes)  # e[5]
            # e.append(HexBytes(y_bytes))
            # print('y_bytes', y_bytes)
            # 此处可以选用在群上直接进行运算
            xx=int.from_bytes(str.encode(xind), byteorder='big')
            # print('------xx-----', xx)
            xtag_w = hmac.new(master_K_X, str.encode(str(gmpy2.powmod(g1, mpz(inv_w) % q, p))), digestmod='md5').hexdigest()  # bytes
            # print('zhuanzhiqian---xtag_w', type(xtag_w), len(xtag_w), xtag_w)
            aa = int.from_bytes(str.encode(xtag_w), byteorder='big', signed=False)
            # print('------aa------', aa)
            xtag_w_xind = ((mpz(aa)% q) * (mpz(xx) % q)) % q
            xtag = gmpy2.powmod(g1, xtag_w_xind, p)
            # testXtag.add(hex(int(xtag)))   # test
            # print('----gax----',xtag)
            # xtag_bytes = str.encode(str(xtag))
            xtag_bytes = Web3.toBytes(hexstr=hex(int(xtag)))
            # print('xtag_bytes', type(xtag_bytes), len(xtag_bytes), xtag_bytes)
            CEDB[u] = e
            CBSIndex.append(xtag_bytes)
            # print('CBSIndex', c, len(CBSIndex), CBSIndex)
        # 此处的c在搜索时如何获得 以数组来存，不需要进行外层运算
        l_st_c.append(st[c])
        # l_st_c.append(str.encode(str(c)))
        l_st_c.append(c)
        # l_st_c.append(cipher)
        # print('check----l_st_c',l_st_c)
        CPT[l] = l_st_c
    print('CEDB------', len(CEDB), CEDB)
    print('CBSIndex------', len(CBSIndex), CBSIndex)
    print('CPT------', len(CPT), CPT)
    return CEDB, CBSIndex, CPT


# 为每个用户生成授权key
# permit_w_set_use = ['wang', 'ming', 'yue']
def user_key_permit(permit_w_set):
    # prime_use = []
    sk_w_all = 1
    for i in permit_w_set:
        sk_w_all = sk_w_all * permit_w_set[i]
        # prime_use.append(kw_prime_file[permit_w_set[i]])
        # sk_w_all = sk_w_all * kw_prime_file[permit_w_set[i]]
    inv_w_all = gmpy2.invert(sk_w_all, q)
    re_sk_w = hmac.new(secret_k, str.encode(str(gmpy2.powmod(g1, mpz(inv_w_all) % q, p))), digestmod='md5').digest()
    print('sk_w', re_sk_w)
    return re_sk_w  # 返回Bytes


def gen_stag_w(query_prime):
    print('----------------------------------Genarate stag_w1')
    inv_w1 = gmpy2.invert(query_prime[0], q)
    # stag_w1
    stag_w_hexstr = hmac.new(secret_k, str.encode(str(gmpy2.powmod(g1, mpz(inv_w1) % q, p))),
                             digestmod='md5').hexdigest()
    stag_w1 = Web3.toBytes(hexstr='0x' + stag_w_hexstr)
    print('stag_w1', type(stag_w1), len(stag_w1), stag_w1, Web3.toHex(stag_w1))
    return stag_w1, stag_w_hexstr


# 为每个用户生成查询token
def search_token(query_prime, c):
    print('----------------------------------Genarate Search Token')
    xtoken = {}
    inv_w1 = gmpy2.invert(query_prime[0], q)
    # stag_w1
    stag_w_hexstr = hmac.new(secret_k, str.encode(str(gmpy2.powmod(g1, mpz(inv_w1) % q, p))), digestmod='md5').hexdigest()
    stag_w1 = Web3.toBytes(hexstr=stag_w_hexstr)
    # print('stag_w1', type(stag_w1), len(stag_w1), stag_w1)
    while c > 0:
        temp_value = []  # 存储每个剩余关键字对应的的xind作为最终的值
        # print('length----query_prime', len(query_prime), c)
        # print('the number of rest keywords in query need to be known before uploading')
        for j in range(1, len(query_prime)):
            # print('query_prime[j]', j, query_prime[j])
            inv_wj = gmpy2.invert(query_prime[j], q)
            # print('inv_wj', type(inv_wj), len(inv_wj), inv_wj)
            z_w1 = gmpy2.powmod(g1, mpz(inv_w1) % q, p)
            temp_z_w1 = hmac.new(master_K_Z, str.encode(str(z_w1) + str(c)), digestmod='md5').hexdigest()
            zz = int.from_bytes(str.encode(temp_z_w1), byteorder='big')
            temp_xind_wj = hmac.new(master_K_X, str.encode(str(gmpy2.powmod(g1, mpz(inv_wj) % q, p))), digestmod='md5').hexdigest()
            aa = int.from_bytes(str.encode(temp_xind_wj), byteorder='big')
            temp_z_xind = ((mpz(aa) % q) * (mpz(zz) % q)) % q
            temp = gmpy2.powmod(g1, temp_z_xind, p)
            temp_bytes = Web3.toBytes(hexstr=hex(int(temp)))
            # print('------token_temp', type(temp_bytes), len(temp_bytes), temp_bytes)
            temp_value.append(temp_bytes)  # bytes
            # print('token_temp_value', type(temp_value), len(temp_value), temp_value)
        xtoken[c] = temp_value  # 每个w1对应c个文件作为键，每个文件与剩余w的关系作为值存储在xtoken中
        # print('xtoken[c]', len(xtoken[c]))
        c = c - 1
    print('xtoken', len(xtoken), xtoken)
    return xtoken


def match(stag_w_hexstr, xtoken, CEDB, CBSIndex, CPT):
    print('-------------------------------------Search')
    R = {}
    D = {}
    # l = str.encode(Web3.keccak(hexstr=stag_w_hexstr).hex())
    l = Web3.keccak(str.encode(stag_w_hexstr))
    # l = Web3.toBytes(Web3.keccak(hexstr=stag_w1).hex())
    # print('l1', l)
    st_c = CPT[l][0]
    # print('stc', str(st_c))
    c = int(CPT[l][1])
    # print('c1', c)
    st = {c: st_c}
    while c > 0:
        list_xtoken_i = xtoken[c]
        # flag = []
        # flag_sum = 0
        e_id = []
        # string_c = str(stag_w1) + str(st[c])
        string_c = stag_w_hexstr + localPad(Web3.toHex(st[c]))[2:]
        # u = str.encode((Web3.keccak(hexstr=string_c)).hex())
        u = Web3.toBytes((Web3.keccak(hexstr=string_c)).hex())
        # print('u1', type(u), len(u), u)
        e = CEDB[u]
        y_bytes = e[5]
        # print('search_y_bytes', y_bytes, type(y_bytes))
        e_id.append(e[0])
        e_id.append(e[1])
        e_id.append(e[2])
        delta = e[3]
        # print('delta', delta, len(delta))
        t_i = e[4]
        # print('t_i', len(t_i), t_i)
        if delta == 1:
            D[u] = e_id
        test_tag = []
        for j in range(len(list_xtoken_i)):
            # print('list_xtoken_i', len(list_xtoken_i), list_xtoken_i[j])
            test_token_y = gmpy2.powmod(mpz(list_xtoken_i[j]), mpz(y_bytes), p)
            bytes_token_y = str.encode(str(test_token_y))
            test_tag.append(bytes_token_y)
        # print(len(test_tag))
            # print('bytes_token_y', bytes_token_y, len(bytes_token_y))
            # print('CBSIndex----------------', CBSIndex, len(CBSIndex))
        # test whether all test tag in CBSIndex
        if all([bytes_token_y in CBSIndex for bytes_token_y in test_tag]):
            R[u] = e_id
        # AES decrypt
        # decipher = AES.new(t_i, AES.MODE_ECB)
        # st[c-1] = unpad(decipher.decrypt(st[c]), BLOCK_SIZE)
        st[c-1] = bytes(a ^ b for a, b in zip(t_i, st[c]))
        c = c - 1
    print('D', len(D), D)
    print('R', len(R), R)
    # R = R.items() - D.items()
    # print(R)
    return R, D


if __name__ == "__main__":
    test_kw_file = {'wang': ['0000000000000000', '283888899990000000', '6242788468561965965166'], 'ming': ['0000000000000000', '283888899990000000', '2100000000008797'], 'yue': ['283888899990000000', '0000000000000000', '16212635411671469']}
    test_kw_prime = {'wang': 21, 'ming': 23, 'yue': 71}
    (pk, sk) = setup()
    (test_CEDB, test_CBSIndex, test_CPT) = build_index(pk, test_kw_file, test_kw_prime)
    test_permit_kw = {'wang': 21, 'ming': 23, 'yue': 71}
    test_sk_w = user_key_permit(test_permit_kw)
    # test_query_kw = [21, 23, 71]
    # # test_query_kw ==> per_query_number
    # per_token_number = 2
    # (test_stag_w, test_stag_w_hex) = gen_stag_w(test_query_kw)
    # test_xtoken = search_token(test_query_kw, c)
    # match(test_stag_w_hex, test_xtoken, test_CEDB, test_CBSIndex, test_CPT)

    # blockchain test
    abi_build_index = """[
	{
		"constant": true,
		"inputs": [
			{
				"name": "R_u",
				"type": "bytes32"
			}
		],
		"name": "get_R_cipher",
		"outputs": [
			{
				"name": "",
				"type": "bytes[]"
			}
		],
		"payable": false,
		"stateMutability": "view",
		"type": "function"
	},
	{
		"constant": false,
		"inputs": [
			{
				"name": "l",
				"type": "bytes32[]"
			},
			{
				"name": "stc",
				"type": "bytes32[]"
			},
			{
				"name": "_len",
				"type": "uint256"
			}
		],
		"name": "set_CPT_stc",
		"outputs": [],
		"payable": false,
		"stateMutability": "nonpayable",
		"type": "function"
	},
	{
		"constant": false,
		"inputs": [
			{
				"name": "p",
				"type": "bytes"
			}
		],
		"name": "setP",
		"outputs": [],
		"payable": false,
		"stateMutability": "nonpayable",
		"type": "function"
	},
	{
		"constant": false,
		"inputs": [
			{
				"name": "u",
				"type": "bytes32[]"
			},
			{
				"name": "y",
				"type": "bytes32[]"
			},
			{
				"name": "len",
				"type": "uint256"
			}
		],
		"name": "set_CEDB_y",
		"outputs": [],
		"payable": false,
		"stateMutability": "nonpayable",
		"type": "function"
	},
	{
		"constant": true,
		"inputs": [
			{
				"name": "",
				"type": "uint256"
			},
			{
				"name": "",
				"type": "uint256"
			}
		],
		"name": "ST_w",
		"outputs": [
			{
				"name": "",
				"type": "bytes"
			}
		],
		"payable": false,
		"stateMutability": "view",
		"type": "function"
	},
	{
		"constant": true,
		"inputs": [
			{
				"name": "",
				"type": "bytes32"
			}
		],
		"name": "CEDB_delta",
		"outputs": [
			{
				"name": "",
				"type": "uint256"
			}
		],
		"payable": false,
		"stateMutability": "view",
		"type": "function"
	},
	{
		"constant": false,
		"inputs": [
			{
				"name": "l",
				"type": "bytes32[]"
			},
			{
				"name": "c",
				"type": "uint256[]"
			},
			{
				"name": "len",
				"type": "uint256"
			}
		],
		"name": "set_CPT_c",
		"outputs": [],
		"payable": false,
		"stateMutability": "nonpayable",
		"type": "function"
	},
	{
		"constant": true,
		"inputs": [
			{
				"name": "",
				"type": "bytes32"
			}
		],
		"name": "CEDB_tc",
		"outputs": [
			{
				"name": "",
				"type": "bytes32"
			}
		],
		"payable": false,
		"stateMutability": "view",
		"type": "function"
	},
	{
		"constant": true,
		"inputs": [
			{
				"name": "u",
				"type": "bytes32"
			}
		],
		"name": "get_CEDB_delta",
		"outputs": [
			{
				"name": "",
				"type": "uint256"
			}
		],
		"payable": false,
		"stateMutability": "view",
		"type": "function"
	},
	{
		"constant": true,
		"inputs": [
			{
				"name": "",
				"type": "uint256"
			}
		],
		"name": "R_cipher",
		"outputs": [
			{
				"name": "",
				"type": "bytes"
			}
		],
		"payable": false,
		"stateMutability": "view",
		"type": "function"
	},
	{
		"constant": false,
		"inputs": [
			{
				"name": "u",
				"type": "bytes32[]"
			},
			{
				"name": "delta",
				"type": "uint256[]"
			},
			{
				"name": "len",
				"type": "uint256"
			}
		],
		"name": "set_CEDB_delta",
		"outputs": [],
		"payable": false,
		"stateMutability": "nonpayable",
		"type": "function"
	},
	{
		"constant": false,
		"inputs": [
			{
				"name": "R_u",
				"type": "bytes32"
			}
		],
		"name": "set_cipher_onebyone",
		"outputs": [],
		"payable": false,
		"stateMutability": "nonpayable",
		"type": "function"
	},
	{
		"constant": true,
		"inputs": [
			{
				"name": "",
				"type": "uint256"
			}
		],
		"name": "st",
		"outputs": [
			{
				"name": "",
				"type": "bytes32"
			}
		],
		"payable": false,
		"stateMutability": "view",
		"type": "function"
	},
	{
		"constant": true,
		"inputs": [
			{
				"name": "u",
				"type": "bytes32"
			}
		],
		"name": "get_CEDB_tc",
		"outputs": [
			{
				"name": "",
				"type": "bytes32"
			}
		],
		"payable": false,
		"stateMutability": "view",
		"type": "function"
	},
	{
		"constant": true,
		"inputs": [
			{
				"name": "b",
				"type": "bytes"
			}
		],
		"name": "CBSIndex_exist",
		"outputs": [
			{
				"name": "",
				"type": "bool"
			}
		],
		"payable": false,
		"stateMutability": "view",
		"type": "function"
	},
	{
		"constant": false,
		"inputs": [
			{
				"name": "R_u",
				"type": "bytes32"
			}
		],
		"name": "set_R_cipher",
		"outputs": [],
		"payable": false,
		"stateMutability": "nonpayable",
		"type": "function"
	},
	{
		"constant": true,
		"inputs": [],
		"name": "getP",
		"outputs": [
			{
				"name": "",
				"type": "bytes"
			}
		],
		"payable": false,
		"stateMutability": "view",
		"type": "function"
	},
	{
		"constant": true,
		"inputs": [
			{
				"name": "",
				"type": "uint256"
			}
		],
		"name": "returnD_u",
		"outputs": [
			{
				"name": "",
				"type": "bytes32"
			}
		],
		"payable": false,
		"stateMutability": "view",
		"type": "function"
	},
	{
		"constant": false,
		"inputs": [
			{
				"name": "u",
				"type": "bytes32[]"
			},
			{
				"name": "t_c",
				"type": "bytes32[]"
			},
			{
				"name": "len",
				"type": "uint256"
			}
		],
		"name": "set_CEDB_tc_batch",
		"outputs": [],
		"payable": false,
		"stateMutability": "nonpayable",
		"type": "function"
	},
	{
		"constant": true,
		"inputs": [
			{
				"name": "",
				"type": "bytes32"
			}
		],
		"name": "CEDB_y",
		"outputs": [
			{
				"name": "",
				"type": "bytes32"
			}
		],
		"payable": false,
		"stateMutability": "view",
		"type": "function"
	},
	{
		"constant": true,
		"inputs": [
			{
				"name": "_x",
				"type": "uint256"
			}
		],
		"name": "toBytes",
		"outputs": [
			{
				"name": "_b",
				"type": "bytes32"
			}
		],
		"payable": false,
		"stateMutability": "view",
		"type": "function"
	},
	{
		"constant": true,
		"inputs": [],
		"name": "get_returnD_u",
		"outputs": [
			{
				"name": "",
				"type": "bytes32[]"
			}
		],
		"payable": false,
		"stateMutability": "view",
		"type": "function"
	},
	{
		"constant": false,
		"inputs": [
			{
				"name": "u",
				"type": "bytes32"
			},
			{
				"name": "t_c",
				"type": "bytes32"
			}
		],
		"name": "set_CEDB_tc",
		"outputs": [],
		"payable": false,
		"stateMutability": "nonpayable",
		"type": "function"
	},
	{
		"constant": true,
		"inputs": [
			{
				"name": "_c",
				"type": "uint256"
			},
			{
				"name": "_index",
				"type": "uint256"
			}
		],
		"name": "get_ST_w",
		"outputs": [
			{
				"name": "",
				"type": "bytes"
			}
		],
		"payable": false,
		"stateMutability": "view",
		"type": "function"
	},
	{
		"constant": true,
		"inputs": [],
		"name": "pp",
		"outputs": [
			{
				"name": "",
				"type": "bytes"
			}
		],
		"payable": false,
		"stateMutability": "view",
		"type": "function"
	},
	{
		"constant": true,
		"inputs": [
			{
				"name": "_l",
				"type": "bytes32"
			}
		],
		"name": "get_CPT_c",
		"outputs": [
			{
				"name": "",
				"type": "uint256"
			}
		],
		"payable": false,
		"stateMutability": "view",
		"type": "function"
	},
	{
		"constant": false,
		"inputs": [
			{
				"name": "xtags",
				"type": "bytes[]"
			},
			{
				"name": "_len",
				"type": "uint256"
			}
		],
		"name": "CBSIndex_add",
		"outputs": [],
		"payable": false,
		"stateMutability": "nonpayable",
		"type": "function"
	},
	{
		"constant": true,
		"inputs": [
			{
				"name": "g",
				"type": "bytes"
			},
			{
				"name": "x",
				"type": "uint256"
			},
			{
				"name": "p",
				"type": "bytes"
			}
		],
		"name": "expmod",
		"outputs": [
			{
				"name": "",
				"type": "bytes"
			}
		],
		"payable": false,
		"stateMutability": "view",
		"type": "function"
	},
	{
		"constant": true,
		"inputs": [
			{
				"name": "_u",
				"type": "bytes32"
			},
			{
				"name": "_index",
				"type": "uint256"
			}
		],
		"name": "get_CEDB_value",
		"outputs": [
			{
				"name": "",
				"type": "bytes"
			}
		],
		"payable": false,
		"stateMutability": "view",
		"type": "function"
	},
	{
		"constant": true,
		"inputs": [
			{
				"name": "",
				"type": "bytes32"
			},
			{
				"name": "",
				"type": "uint256"
			}
		],
		"name": "CEDB",
		"outputs": [
			{
				"name": "",
				"type": "bytes"
			}
		],
		"payable": false,
		"stateMutability": "view",
		"type": "function"
	},
	{
		"constant": true,
		"inputs": [
			{
				"name": "_a",
				"type": "bytes16"
			},
			{
				"name": "_b",
				"type": "bytes32"
			}
		],
		"name": "concate",
		"outputs": [
			{
				"name": "",
				"type": "bytes"
			}
		],
		"payable": false,
		"stateMutability": "view",
		"type": "function"
	},
	{
		"constant": true,
		"inputs": [],
		"name": "get_returnR_u",
		"outputs": [
			{
				"name": "",
				"type": "bytes32[]"
			}
		],
		"payable": false,
		"stateMutability": "view",
		"type": "function"
	},
	{
		"constant": false,
		"inputs": [
			{
				"name": "_u",
				"type": "bytes32[]"
			},
			{
				"name": "_C_0",
				"type": "bytes[]"
			},
			{
				"name": "_C_1",
				"type": "bytes[]"
			},
			{
				"name": "_C_2",
				"type": "bytes[]"
			},
			{
				"name": "_y",
				"type": "bytes[]"
			},
			{
				"name": "_len",
				"type": "uint256"
			}
		],
		"name": "set_CEDB_batch",
		"outputs": [],
		"payable": false,
		"stateMutability": "nonpayable",
		"type": "function"
	},
	{
		"constant": true,
		"inputs": [
			{
				"name": "",
				"type": "uint256"
			},
			{
				"name": "",
				"type": "uint256"
			}
		],
		"name": "cipher_onebyone",
		"outputs": [
			{
				"name": "",
				"type": "bytes"
			}
		],
		"payable": false,
		"stateMutability": "view",
		"type": "function"
	},
	{
		"constant": true,
		"inputs": [
			{
				"name": "",
				"type": "uint256"
			}
		],
		"name": "returnR_u",
		"outputs": [
			{
				"name": "",
				"type": "bytes32"
			}
		],
		"payable": false,
		"stateMutability": "view",
		"type": "function"
	},
	{
		"constant": true,
		"inputs": [
			{
				"name": "u",
				"type": "bytes32"
			}
		],
		"name": "get_CEDB_y",
		"outputs": [
			{
				"name": "",
				"type": "bytes32"
			}
		],
		"payable": false,
		"stateMutability": "view",
		"type": "function"
	},
	{
		"constant": false,
		"inputs": [
			{
				"name": "_c",
				"type": "uint256"
			},
			{
				"name": "_searchtoken",
				"type": "bytes[]"
			},
			{
				"name": "_per_token_number",
				"type": "uint256"
			}
		],
		"name": "set_ST_w",
		"outputs": [],
		"payable": false,
		"stateMutability": "nonpayable",
		"type": "function"
	},
	{
		"constant": true,
		"inputs": [
			{
				"name": "",
				"type": "bytes32"
			}
		],
		"name": "CPT_stc",
		"outputs": [
			{
				"name": "",
				"type": "bytes32"
			}
		],
		"payable": false,
		"stateMutability": "view",
		"type": "function"
	},
	{
		"constant": true,
		"inputs": [
			{
				"name": "_l",
				"type": "bytes32"
			}
		],
		"name": "get_CPT_stc",
		"outputs": [
			{
				"name": "",
				"type": "bytes32"
			}
		],
		"payable": false,
		"stateMutability": "view",
		"type": "function"
	},
	{
		"constant": true,
		"inputs": [
			{
				"name": "",
				"type": "bytes32"
			}
		],
		"name": "CPT_c",
		"outputs": [
			{
				"name": "",
				"type": "uint256"
			}
		],
		"payable": false,
		"stateMutability": "view",
		"type": "function"
	},
	{
		"constant": false,
		"inputs": [
			{
				"name": "stag_w",
				"type": "bytes16"
			},
			{
				"name": "st_c",
				"type": "bytes32"
			},
			{
				"name": "c",
				"type": "uint256"
			},
			{
				"name": "per_token_number",
				"type": "uint256"
			}
		],
		"name": "onchain_search",
		"outputs": [],
		"payable": false,
		"stateMutability": "nonpayable",
		"type": "function"
	},
	{
		"constant": true,
		"inputs": [
			{
				"name": "c",
				"type": "uint256"
			}
		],
		"name": "get_st",
		"outputs": [
			{
				"name": "",
				"type": "bytes32"
			}
		],
		"payable": false,
		"stateMutability": "view",
		"type": "function"
	},
	{
		"constant": false,
		"inputs": [
			{
				"name": "_u",
				"type": "bytes32"
			},
			{
				"name": "_C_0",
				"type": "bytes"
			},
			{
				"name": "_C_1",
				"type": "bytes"
			},
			{
				"name": "_C_2",
				"type": "bytes"
			}
		],
		"name": "set_CEDB",
		"outputs": [],
		"payable": false,
		"stateMutability": "nonpayable",
		"type": "function"
	},
	{
		"constant": true,
		"inputs": [
			{
				"name": "R_u",
				"type": "bytes32"
			}
		],
		"name": "get_cipher_onebyone",
		"outputs": [
			{
				"name": "",
				"type": "bytes[][]"
			}
		],
		"payable": false,
		"stateMutability": "view",
		"type": "function"
	}
]"""
    from_account = w3.toChecksumAddress("0x3c62Aa7913bc303ee4B9c07Df87B556B6770E3fC")
    abi_build_index = json.loads(abi_build_index)
    store_var_contract = w3.eth.contract(address=w3.toChecksumAddress('0x903b76aF4e3a88D27148905D1a8141D84657ac65'), abi=abi_build_index)

    p_hex = hex(int(p))
    tx_setP_hash = store_var_contract.functions.setP(p_hex).transact(
        {"from": from_account, "gas": 3000000, "gasPrice": 0})
    tx_receipt = w3.eth.waitForTransactionReceipt(tx_setP_hash)
    print('---------setP', tx_receipt.status, tx_receipt.gasUsed)

    len_test_CEDB = len(test_CEDB)
    print('CEDB len', len_test_CEDB)
    u_list = []
    C_0_list = []
    C_1_list = []
    C_2_list = []
    delta_list = []
    tc_list = []
    y_list = []
    for key in test_CEDB:
        u_list.append(key)
        C_0_list.append(test_CEDB[key][0])
        C_1_list.append(test_CEDB[key][1])
        C_2_list.append(test_CEDB[key][2])
        delta_list.append(test_CEDB[key][3])
        tc_list.append(test_CEDB[key][4])
        y_list.append(test_CEDB[key][5])
        # print('CEDB key', type(key), key)
        # print('test_CEDB[key][0]', type(test_CEDB[key][1]), test_CEDB[key][1])
    tx_set_CEDB_batch_hash = store_var_contract.functions.set_CEDB_batch(u_list, C_0_list, C_1_list, C_2_list, y_list, len_test_CEDB).transact({"from": from_account, "gas": 80000000000000, "gasPrice": 0})
    tx_receipt = w3.eth.waitForTransactionReceipt(tx_set_CEDB_batch_hash)
    print('---------set CEDB', tx_receipt.status, tx_receipt.gasUsed)
    tx_CEDB_tc_batch_hash = store_var_contract.functions.set_CEDB_tc_batch(u_list, tc_list, len_test_CEDB).transact({"from": from_account, "gas": 80000000000, "gasPrice": 0})
    tx_receipt = w3.eth.waitForTransactionReceipt(tx_CEDB_tc_batch_hash)
    print('---------setCEDB_tc', tx_receipt.status, tx_receipt.gasUsed)
    tx_CEDB_delta_hash = store_var_contract.functions.set_CEDB_delta(u_list, delta_list, len_test_CEDB).transact(
        {"from": from_account, "gas": 80000000000, "gasPrice": 0})
    tx_receipt = w3.eth.waitForTransactionReceipt(tx_CEDB_delta_hash)
    print('---------setCEDB_delta', tx_receipt.status, tx_receipt.gasUsed)
    tx_CEDB_y_hash = store_var_contract.functions.set_CEDB_y(u_list, y_list, len_test_CEDB).transact(
        {"from": from_account, "gas": 80000000000, "gasPrice": 0})
    tx_receipt = w3.eth.waitForTransactionReceipt(tx_CEDB_y_hash)
    print('---------setCEDB_y', tx_receipt.status, tx_receipt.gasUsed)

    len_test_CBSIndex = len(test_CBSIndex)
    print('len_test_CBSIndex', len_test_CBSIndex)
    # CBSSet = [i for i in test_CBSIndex]
    tx_CBSIndex_add_hash = store_var_contract.functions.CBSIndex_add(test_CBSIndex, len_test_CBSIndex).transact({"from": from_account, "gas": 80000000000, "gasPrice": 0})
    tx_receipt = w3.eth.waitForTransactionReceipt(tx_CBSIndex_add_hash)
    print('---------setCBSIndex', tx_receipt.status, tx_receipt.gasUsed)

    len_CPT = len(test_CPT)
    print('len_CPT', len_CPT)
    CPT_l = []
    CPT_stc = []
    CPT_c = []
    for i in test_CPT.keys():
        CPT_l.append(i)
        CPT_stc.append(test_CPT[i][0])
        CPT_c.append(test_CPT[i][1])
    tx_set_CPT_stc_hash = store_var_contract.functions.set_CPT_stc(CPT_l, CPT_stc, len_CPT).transact(
        {"from": from_account, "gas": 80000000000, "gasPrice": 0})
    tx_receipt = w3.eth.waitForTransactionReceipt(tx_set_CPT_stc_hash)
    print('---------setCPT_stc', tx_receipt.status, tx_receipt.gasUsed)
    tx_set_CPT_c_hash = store_var_contract.functions.set_CPT_c(CPT_l, CPT_c, len_CPT).transact(
        {"from": from_account, "gas": 80000000000, "gasPrice": 0})
    tx_receipt = w3.eth.waitForTransactionReceipt(tx_set_CPT_c_hash)
    print('---------setCPT_c', tx_receipt.status, tx_receipt.gasUsed)

    test_query_kw = [21, 23, 71]
    # test_query_kw ==> per_query_number
    per_token_number = 2
    (test_stag_w, test_stag_w_hex) = gen_stag_w(test_query_kw)
    # stag_w ==> l ==> stc, c
    l = Web3.keccak(str.encode(test_stag_w_hex))
    tx_get_CPT_stc_hash = store_var_contract.functions.get_CPT_stc(l).transact(
        {"from": from_account, "gas": 3000000, "gasPrice": 0})
    tx_receipt = w3.eth.waitForTransactionReceipt(tx_get_CPT_stc_hash)
    st_c = store_var_contract.functions.get_CPT_stc(l).call()
    print('---------getCPT_stc', tx_receipt.status, tx_receipt.gasUsed, st_c, Web3.toHex(st_c))
    tx_get_CPT_c_hash = store_var_contract.functions.get_CPT_c(l).transact(
        {"from": from_account, "gas": 3000000, "gasPrice": 0})
    tx_receipt = w3.eth.waitForTransactionReceipt(tx_get_CPT_c_hash)
    c = store_var_contract.functions.get_CPT_c(l).call()
    print('---------getCPT_c', tx_receipt.status, tx_receipt.gasUsed, c)

    test_xtoken = search_token(test_query_kw, c)
    # match(test_stag_w_hex, test_xtoken, test_CEDB, test_CBSIndex, test_CPT)
    # searchtoken = []
    # for i in test_xtoken.keys():
    #     searchtoken.append(test_xtoken[i])
    print('-----------Onchain Search')
    # for i in range(1, c+1):
    while_c = c
    while while_c > 0:
        tx_set_ST_w_hash = store_var_contract.functions.set_ST_w(while_c, test_xtoken[while_c], per_token_number).transact(
            {"from": from_account, "gas": 300000000, "gasPrice": 0})
        tx_receipt = w3.eth.waitForTransactionReceipt(tx_set_ST_w_hash)
        print('---------set_ST_w', tx_receipt.status, tx_receipt.gasUsed)
        while_c = while_c - 1

    # test xtag exist
    # getST_w = store_var_contract.functions.get_ST_w(1, 0).call()
    # print('ST[1][1]', len(test_xtoken[1][0]), Web3.toHex(test_xtoken[1][0]))
    # print('getST_w', len(getST_w),  Web3.toHex(getST_w))
    # get_y_bytes = store_var_contract.functions.get_CEDB_y(u_list[2]).call()
    # print('y', len(y_list[2]), Web3.toHex(y_list[2]))
    # print('get_y_bytes', len(get_y_bytes), Web3.toHex(get_y_bytes))
    # # get_y_int = Web3.toInt(hexstr=str(Web3.toHex(get_y_bytes)))
    # get_y_int = Web3.toInt(get_y_bytes)
    # print('get_y_int', get_y_int)
    # getPP = store_var_contract.functions.getP().call()
    # print('getPP', len(getPP), Web3.toHex(getPP))
    #
    # tx_expmod_hash = store_var_contract.functions.expmod(getST_w, get_y_int, getPP).transact(
    #     {"from": from_account, "gas": 800000000, "gasPrice": 0})
    # tx_receipt = w3.eth.waitForTransactionReceipt(tx_expmod_hash)
    # print('---------onchain_expod', tx_receipt.status, tx_receipt.gasUsed)
    # get_expod_result = store_var_contract.functions.expmod(getST_w, get_y_int, getPP).call()
    # # print('get_expod_result', get_expod_result)
    # print('get_expod_result', Web3.toHex(get_expod_result))
    # print('CBSIndex[3]', Web3.toHex(test_CBSIndex[2]))
    #
    # tx_CBSIndex_exist_hash = store_var_contract.functions.CBSIndex_exist(get_expod_result).transact(
    #         {"from": from_account, "gas": 300000000, "gasPrice": 0})
    # tx_receipt = w3.eth.waitForTransactionReceipt(tx_set_ST_w_hash)
    # get_CBSIndex_exist = store_var_contract.functions.CBSIndex_exist(get_expod_result).call()
    # print('---------get_CBSIndex_exist', tx_receipt.status, tx_receipt.gasUsed, get_CBSIndex_exist)

    tx_onchain_search_hash = store_var_contract.functions.onchain_search(test_stag_w, st_c, c, per_token_number).transact(
        {"from": from_account, "gas": 800000000, "gasPrice": 0})
    tx_receipt = w3.eth.waitForTransactionReceipt(tx_onchain_search_hash)
    print('---------onchain_search', tx_receipt.status, tx_receipt.gasUsed)
    # get_y_flag_all = store_var_contract.functions.get_y_flag_all().call()
    # print('get_y_flag_all', len(get_y_flag_all), get_y_flag_all)
    testR = store_var_contract.functions.get_returnR_u().call()
    print('testR', type(testR), len(testR), testR)


    # test xor and blockchain
    # def testPad(a):
    #     # b = hex(int(bytes.decode(a), 2))
    #     # b = b[2:]
    #     b = hex(int(a, 2))[2:]
    #     return "0x" + '0' * (64 - len(b)) + b

    # byte1 = random_string(random_length)
    # print('byte1', type(byte1), len(byte1), byte1)
    # byte1_hex = testPad(byte1)
    # # byte1_hex = Web3.toHex(str.encode(byte1))
    # print('byte1_hex', type(byte1_hex), len(byte1_hex), byte1_hex)
    # # byte1_hex_bytes = str.encode(byte1_hex)
    # byte1_hex_bytes = Web3.toBytes(hexstr=byte1_hex)
    # print('byte1_hex_bytes', type(byte1_hex_bytes), len(byte1_hex_bytes), byte1_hex_bytes)
    #
    # byte2 = random_string(random_length)
    # print('byte2', type(byte2), len(byte2), byte2)
    # byte2_hex = testPad(byte2)
    # print('byte2_hex', type(byte2_hex), len(byte2_hex), byte2_hex)
    # # byte2_hex_bytes = str.encode(byte2_hex)
    # byte2_hex_bytes = Web3.toBytes(hexstr=byte2_hex)
    # print('byte2_hex_bytes', type(byte2_hex_bytes), len(byte2_hex_bytes), byte2_hex_bytes)
    # # xor
    # cipher = bytes(a ^ b for a, b in zip(byte1_hex_bytes, byte2_hex_bytes))
    # print('cipher', type(cipher), len(cipher), cipher)
    # decipher = bytes(a ^ b for a, b in zip(byte1_hex_bytes, cipher))
    # print(decipher)

# abi_build_index = '''[
# {
#     "constant": false,
#     "inputs": [
#         {
#             "name": "b",
#             "type": "bytes"
#         }
#     ],
#     "name": "bytesToUint",
#     "outputs": [
#         {
#             "name": "",
#             "type": "uint256"
#         }
#     ],
#     "payable": false,
#     "stateMutability": "nonpayable",
#     "type": "function"
# },
# {
#     "constant": false,
#     "inputs": [
#         {
#             "name": "p",
#             "type": "bytes"
#         }
#     ],
#     "name": "setP",
#     "outputs": [],
#     "payable": false,
#     "stateMutability": "nonpayable",
#     "type": "function"
# },
# {
#     "constant": true,
#     "inputs": [],
#     "name": "get_byte2",
#     "outputs": [
#         {
#             "name": "",
#             "type": "bytes32"
#         }
#     ],
#     "payable": false,
#     "stateMutability": "view",
#     "type": "function"
# },
# {
#     "constant": true,
#     "inputs": [],
#     "name": "xor_cipher",
#     "outputs": [
#         {
#             "name": "",
#             "type": "bytes32"
#         }
#     ],
#     "payable": false,
#     "stateMutability": "view",
#     "type": "function"
# },
# {
#     "constant": true,
#     "inputs": [
#         {
#             "name": "",
#             "type": "uint256"
#         },
#         {
#             "name": "",
#             "type": "uint256"
#         }
#     ],
#     "name": "ST_w",
#     "outputs": [
#         {
#             "name": "",
#             "type": "bytes"
#         }
#     ],
#     "payable": false,
#     "stateMutability": "view",
#     "type": "function"
# },
# {
#     "constant": true,
#     "inputs": [
#         {
#             "name": "",
#             "type": "bytes32"
#         },
#         {
#             "name": "",
#             "type": "uint256"
#         }
#     ],
#     "name": "R",
#     "outputs": [
#         {
#             "name": "",
#             "type": "bytes"
#         }
#     ],
#     "payable": false,
#     "stateMutability": "view",
#     "type": "function"
# },
# {
#     "constant": true,
#     "inputs": [
#         {
#             "name": "",
#             "type": "bytes32"
#         },
#         {
#             "name": "",
#             "type": "uint256"
#         }
#     ],
#     "name": "CPT",
#     "outputs": [
#         {
#             "name": "",
#             "type": "bytes"
#         }
#     ],
#     "payable": false,
#     "stateMutability": "view",
#     "type": "function"
# },
# {
#     "constant": false,
#     "inputs": [
#         {
#             "name": "_u",
#             "type": "bytes32"
#         },
#         {
#             "name": "_C_0",
#             "type": "bytes"
#         },
#         {
#             "name": "_C_1",
#             "type": "bytes"
#         },
#         {
#             "name": "_C_2",
#             "type": "bytes"
#         },
#         {
#             "name": "_delta",
#             "type": "bytes"
#         },
#         {
#             "name": "_t_c",
#             "type": "bytes"
#         },
#         {
#             "name": "_y",
#             "type": "bytes"
#         }
#     ],
#     "name": "set_CEDB",
#     "outputs": [],
#     "payable": false,
#     "stateMutability": "nonpayable",
#     "type": "function"
# },
# {
#     "constant": true,
#     "inputs": [],
#     "name": "test_byte1",
#     "outputs": [
#         {
#             "name": "",
#             "type": "bytes32"
#         }
#     ],
#     "payable": false,
#     "stateMutability": "view",
#     "type": "function"
# },
# {
#     "constant": true,
#     "inputs": [
#         {
#             "name": "",
#             "type": "uint256"
#         }
#     ],
#     "name": "st",
#     "outputs": [
#         {
#             "name": "",
#             "type": "bytes16"
#         }
#     ],
#     "payable": false,
#     "stateMutability": "view",
#     "type": "function"
# },
# {
#     "constant": true,
#     "inputs": [
#         {
#             "name": "b",
#             "type": "bytes"
#         }
#     ],
#     "name": "CBSIndex_exist",
#     "outputs": [
#         {
#             "name": "",
#             "type": "bool"
#         }
#     ],
#     "payable": false,
#     "stateMutability": "view",
#     "type": "function"
# },
# {
#     "constant": true,
#     "inputs": [],
#     "name": "get_xor",
#     "outputs": [
#         {
#             "name": "",
#             "type": "bytes32"
#         }
#     ],
#     "payable": false,
#     "stateMutability": "view",
#     "type": "function"
# },
# {
#     "constant": true,
#     "inputs": [
#         {
#             "name": "_a",
#             "type": "bytes16"
#         },
#         {
#             "name": "_b",
#             "type": "bytes16"
#         }
#     ],
#     "name": "concate",
#     "outputs": [
#         {
#             "name": "",
#             "type": "bytes"
#         }
#     ],
#     "payable": false,
#     "stateMutability": "view",
#     "type": "function"
# },
# {
#     "constant": true,
#     "inputs": [
#         {
#             "name": "_l",
#             "type": "bytes32"
#         },
#         {
#             "name": "_index",
#             "type": "uint256"
#         }
#     ],
#     "name": "get_CPT",
#     "outputs": [
#         {
#             "name": "",
#             "type": "bytes"
#         }
#     ],
#     "payable": false,
#     "stateMutability": "view",
#     "type": "function"
# },
# {
#     "constant": true,
#     "inputs": [],
#     "name": "stag_w",
#     "outputs": [
#         {
#             "name": "",
#             "type": "bytes16"
#         }
#     ],
#     "payable": false,
#     "stateMutability": "view",
#     "type": "function"
# },
# {
#     "constant": true,
#     "inputs": [
#         {
#             "name": "_x",
#             "type": "uint256"
#         }
#     ],
#     "name": "toBytes",
#     "outputs": [
#         {
#             "name": "_b",
#             "type": "bytes32"
#         }
#     ],
#     "payable": false,
#     "stateMutability": "view",
#     "type": "function"
# },
# {
#     "constant": false,
#     "inputs": [
#         {
#             "name": "_u",
#             "type": "bytes32[]"
#         },
#         {
#             "name": "_C_0",
#             "type": "bytes[]"
#         },
#         {
#             "name": "_C_1",
#             "type": "bytes[]"
#         },
#         {
#             "name": "_C_2",
#             "type": "bytes[]"
#         },
#         {
#             "name": "_delta",
#             "type": "bytes[]"
#         },
#         {
#             "name": "_t_c",
#             "type": "bytes[]"
#         },
#         {
#             "name": "_y",
#             "type": "bytes[]"
#         },
#         {
#             "name": "_len",
#             "type": "uint256"
#         }
#     ],
#     "name": "set_CEDB_batch",
#     "outputs": [],
#     "payable": false,
#     "stateMutability": "nonpayable",
#     "type": "function"
# },
# {
#     "constant": true,
#     "inputs": [
#         {
#             "name": "_c",
#             "type": "uint256"
#         },
#         {
#             "name": "_index",
#             "type": "uint256"
#         }
#     ],
#     "name": "get_ST_w",
#     "outputs": [
#         {
#             "name": "",
#             "type": "bytes"
#         }
#     ],
#     "payable": false,
#     "stateMutability": "view",
#     "type": "function"
# },
# {
#     "constant": false,
#     "inputs": [
#         {
#             "name": "_stag_w",
#             "type": "bytes16"
#         },
#         {
#             "name": "_st_c",
#             "type": "bytes16"
#         },
#         {
#             "name": "_per_token_number",
#             "type": "uint256"
#         }
#     ],
#     "name": "onchain_search",
#     "outputs": [],
#     "payable": false,
#     "stateMutability": "nonpayable",
#     "type": "function"
# },
# {
#     "constant": true,
#     "inputs": [],
#     "name": "pp",
#     "outputs": [
#         {
#             "name": "",
#             "type": "bytes"
#         }
#     ],
#     "payable": false,
#     "stateMutability": "view",
#     "type": "function"
# },
# {
#     "constant": false,
#     "inputs": [
#         {
#             "name": "xtags",
#             "type": "bytes[]"
#         },
#         {
#             "name": "_len",
#             "type": "uint256"
#         }
#     ],
#     "name": "CBSIndex_add",
#     "outputs": [],
#     "payable": false,
#     "stateMutability": "nonpayable",
#     "type": "function"
# },
# {
#     "constant": true,
#     "inputs": [
#         {
#             "name": "g",
#             "type": "bytes"
#         },
#         {
#             "name": "x",
#             "type": "bytes"
#         },
#         {
#             "name": "p",
#             "type": "bytes"
#         }
#     ],
#     "name": "expmod",
#     "outputs": [
#         {
#             "name": "",
#             "type": "bytes"
#         }
#     ],
#     "payable": false,
#     "stateMutability": "view",
#     "type": "function"
# },
# {
#     "constant": true,
#     "inputs": [
#         {
#             "name": "_u",
#             "type": "bytes32"
#         },
#         {
#             "name": "_index",
#             "type": "uint256"
#         }
#     ],
#     "name": "get_CEDB_value",
#     "outputs": [
#         {
#             "name": "",
#             "type": "bytes"
#         }
#     ],
#     "payable": false,
#     "stateMutability": "view",
#     "type": "function"
# },
# {
#     "constant": true,
#     "inputs": [
#         {
#             "name": "",
#             "type": "bytes32"
#         },
#         {
#             "name": "",
#             "type": "uint256"
#         }
#     ],
#     "name": "CEDB",
#     "outputs": [
#         {
#             "name": "",
#             "type": "bytes"
#         }
#     ],
#     "payable": false,
#     "stateMutability": "view",
#     "type": "function"
# },
# {
#     "constant": true,
#     "inputs": [
#         {
#             "name": "",
#             "type": "bytes32"
#         },
#         {
#             "name": "",
#             "type": "uint256"
#         }
#     ],
#     "name": "D",
#     "outputs": [
#         {
#             "name": "",
#             "type": "bytes"
#         }
#     ],
#     "payable": false,
#     "stateMutability": "view",
#     "type": "function"
# },
# {
#     "constant": false,
#     "inputs": [
#         {
#             "name": "_c",
#             "type": "uint256"
#         },
#         {
#             "name": "_searchtoken",
#             "type": "bytes[]"
#         },
#         {
#             "name": "_per_token_number",
#             "type": "uint256"
#         }
#     ],
#     "name": "set_ST_w",
#     "outputs": [],
#     "payable": false,
#     "stateMutability": "nonpayable",
#     "type": "function"
# },
# {
#     "constant": true,
#     "inputs": [],
#     "name": "get_byte1",
#     "outputs": [
#         {
#             "name": "",
#             "type": "bytes32"
#         }
#     ],
#     "payable": false,
#     "stateMutability": "view",
#     "type": "function"
# },
# {
#     "constant": false,
#     "inputs": [
#         {
#             "name": "byte1",
#             "type": "bytes32"
#         },
#         {
#             "name": "byte2",
#             "type": "bytes32"
#         }
#     ],
#     "name": "x_o_r",
#     "outputs": [],
#     "payable": false,
#     "stateMutability": "nonpayable",
#     "type": "function"
# },
# {
#     "constant": true,
#     "inputs": [],
#     "name": "test_byte2",
#     "outputs": [
#         {
#             "name": "",
#             "type": "bytes32"
#         }
#     ],
#     "payable": false,
#     "stateMutability": "view",
#     "type": "function"
# },
# {
#     "constant": false,
#     "inputs": [
#         {
#             "name": "_l",
#             "type": "bytes32[]"
#         },
#         {
#             "name": "_stc",
#             "type": "bytes[]"
#         },
#         {
#             "name": "_c",
#             "type": "bytes[]"
#         },
#         {
#             "name": "_len",
#             "type": "uint256"
#         }
#     ],
#     "name": "set_CPT",
#     "outputs": [],
#     "payable": false,
#     "stateMutability": "nonpayable",
#     "type": "function"
# }
# ]'''


# from_account = w3.toChecksumAddress("0x3c62Aa7913bc303ee4B9c07Df87B556B6770E3fC")
# abi_build_index = json.loads(abi_build_index)
# store_var_contract = w3.eth.contract(address=w3.toChecksumAddress('0xcCf6BABA2eB54583Ec3541A333964850709569f7'), abi=abi_build_index)
#
# test_fun_xor = store_var_contract.functions.x_o_r(byte1_hex_bytes, cipher).transact({"from": from_account, "gas": 30000000, "gasPrice": 0})
# tx_receipt = w3.eth.waitForTransactionReceipt(test_fun_xor)
# xor_value = store_var_contract.functions.get_xor().call()
# print('test_xor_value', type(Web3.toHex(xor_value)), Web3.toHex(xor_value))
# byte1_value = store_var_contract.functions.get_byte1().call()
# print('byte1_value', type(Web3.toHex(byte1_value)), len(Web3.toHex(byte1_value)), Web3.toHex(byte1_value))
# byte2_value = store_var_contract.functions.get_byte2().call()
# print('byte2_value', type(Web3.toHex(byte2_value)), len(Web3.toHex(byte2_value)), Web3.toHex(byte2_value))

    # key = 'abcdefghijklmnop'
    # cipher = AES.new(key.encode('utf8'), AES.MODE_ECB)
    # msg = cipher.encrypt(pad(b'hello', BLOCK_SIZE))
    # print(msg.hex())
    # decipher = AES.new(key.encode('utf8'), AES.MODE_ECB)
    # msg_dec = decipher.decrypt(msg)
    # print(unpad(msg_dec, BLOCK_SIZE))

    # file_id_GT(pk, '7997890000')

    # print(random_string(random_length))
    # kw_to_primes()

    # gmpy2.powmod(6, 4, 3)
