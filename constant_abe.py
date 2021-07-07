import random
from pypbc import *
from datetime import datetime

debug = False


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
    # c1='1'+str(hash_value_x_t)
    # c2 ='2'+ str(hash_value_x_t)
    # hash_value_x_t = Element.from_hash(pairing, Zr,c1)
    # print('11', hash_value_x_t)
    # hash_value_x_t = Element.from_hash(pairing, Zr, c2)
    # print('22', hash_value_x_t)

    # print(hash_value_x_t)

    # define global attributes
    # attr_list = ['ONE', 'TWO']  # 2 attr
    # attr_value = [['A', 'B', 'C'], ['D', 'E']]
    # attr_list = ['ONE', 'TWO', 'THREE', 'FOUR']  # 4 attr
    # attr_value = [['A', 'B', 'C'], ['D', 'E'], ['F', 'G', 'H'], ['I', 'J']]
    # attr_list = ['ONE', 'TWO', 'THREE', 'FOUR', 'FIVE', 'SIX', 'SEVEN', 'EIGHT']  # 8 attr
    # attr_value = [['A', 'B', 'C'], ['D', 'E'], ['F', 'G', 'H'], ['I', 'J'], ['K'], ['L', 'I'], ['K', 'L'], ['O', 'P', 'Q']]
    attr_list = ['ONE', 'TWO', 'THREE', 'FOUR', 'FIVE', 'SIX', 'SEVEN', 'EIGHT', 'NINE', 'TEN', 'ELEVEN', 'TWELVE', 'THIRTEEN', 'FOURTEEN', 'FIFTEEN', 'SIXTEEN']  # 16 attr
    attr_value = [['A', 'B', 'C'], ['D', 'E'], ['F', 'G', 'H'], ['I', 'J'], ['K'], ['L', 'I'], ['K', 'L'],
                  ['O', 'P', 'Q'], ['A', 'B', 'C'], ['D', 'E'], ['F', 'G', 'H'], ['I', 'J'], ['K'], ['L', 'I'], ['K', 'L'],
                  ['O', 'P', 'Q']]


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
    # attr_L = {0: [0, 1], 1: [0]}  # 2 attr
    # attr_L = {0: [0, 1], 1: [0], 2: [0], 3: [0, 1]}  # 4 attr
    # attr_L = {0: [0, 1], 1: [0], 2: [0], 3: [0, 1], 4: [0, 1], 5: [0], 6: [0, 1], 7: [0]}  # 8 attr
    attr_L = {0: [0, 1], 1: [0], 2: [0], 3: [0, 1], 4: [0, 1], 5: [0], 6: [0, 1], 7: [0], 8: [0, 1],
              9: [0], 10: [0], 11: [0, 1], 12: [0, 1], 13: [0], 14: [0, 1], 15: [0, 1, 2]}  # 16 attr

    # random sk
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

    # policy_W = {0: [0, 1], 1: [0]}  # 2 attr
    policy_W = {0: [0, 1], 1: [0], 2: [0], 3: [0, 1]}  # 4 attr
    # policy_W = {0: [0, 1], 1: [0], 2: [0], 3: [0, 1], 4: [0, 1], 5: [0], 6: [0, 1], 7: [0]}  # 8 attr
    # policy_W = {0: [0, 1], 1: [0], 2: [0], 3: [0, 1], 4: [0, 1], 5: [0], 6: [0], 7: [0], 8: [0, 1],
    #  9: [0], 10: [0], 11: [0, 1], 12: [0, 1], 13: [0], 14: [0, 1], 15: [0, 1]}  # 16 attr


    g = pk['g']
    pairing = pk['pairing']
    X = pk['X']
    Y = pk['Y']
    # random s
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
    # print('dec_M', M)

    return M


if __name__ == '__main__':
    start_setup = datetime.now()
    (pk, msk) = setup()
    end_setup = datetime.now()
    print('--------setup time', end_setup - start_setup)
    g = pk['g']
    # print('g', g)
    pairing = pk['pairing']
    X = pk['X']
    # print(X)
    start_keygen = datetime.now()
    SK_L = keygen(pk, msk)
    end_keygen = datetime.now()
    print('--------keygen time', end_keygen - start_keygen)
    # print('keygen')
    # print(SK_L)
    M = Element(pairing, GT)
    M = pairing.apply(g, g)
    s = random.randint(10, 1000)
    M = Element(pairing, GT, value=M ** s)
    # print('enc_M', M)
    start_encrypt = datetime.now()
    CT_W = encrypt(pk, M)
    end_encrypt = datetime.now()
    print('--------encrypt time', end_encrypt - start_encrypt)
    start_decrypt = datetime.now()
    dec_M = decrypt(pk, CT_W, SK_L)
    end_decrypt = datetime.now()
    print('--------decrypt time', end_decrypt - start_decrypt)

    # policy_W = {0: [0, 1], 2: [2]}
    # for i in policy_W:
    #     list_X_i = X[i]
    #     print(list_X_i)
    #     for j in range(len(policy_W[i])):
    #         k_i = policy_W[i][j]
    #         print(k_i)
    #         print(list_X_i[k_i])
    #     print(i)

    # string_test = 'test'
    # print(str.encode(string_test), string_test)
    #
    # attr_L = {'0': [0, 1], '2': [2,10]}
    # test = {}
    # for i in attr_L:
    # list_sigma = []
    # for k_i in range(len(attr_L[i])):
    #     print(i, attr_L[i][k_i])
    # test[i] = list_sigma
