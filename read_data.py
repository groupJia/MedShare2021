import numpy as np
import time
import os
from scipy.sparse import csr_matrix
import re
import random
import hmac
import hmac
import random
from Crypto.Cipher import AES
import pickle
import string
import gmpy2

file_amount = 123

# load 10 file 500 id
# load 15 file 1000 id
# load 31 file 2000 id
# load 64 file 4000 id
# load 123 file 8000 id




stopWords = {'ourselves', 'hers', 'between', 'yourself', 'but', 'again', 'there', 'about', 'once', 'during', 'out',
             'very', 'having', 'with', 'they', 'own', 'an', 'be', 'some', 'for', 'do', 'its', 'yours', 'such',
             'into',
             'of', 'most', 'itself', 'other', 'off', 'is', 's', 'am', 'or', 'who', 'as', 'from', 'him', 'each',
             'the',
             'themselves', 'until', 'below', 'are', 'we', 'these', 'your', 'his', 'through', 'don', 'nor', 'me',
             'were', 'her', 'more', 'himself', 'this', 'down', 'should', 'our', 'their', 'while', 'above', 'both',
             'up', 'to', 'ours', 'had', 'she', 'all', 'no', 'when', 'at', 'any', 'before', 'them', 'same', 'and',
             'been', 'have', 'in', 'will', 'on', 'does', 'yourselves', 'then', 'that', 'because', 'what', 'over',
             'why', 'so', 'can', 'did', 'not', 'now', 'under', 'he', 'you', 'herself', 'has', 'just', 'where',
             'too',
             'only', 'myself', 'which', 'those', 'i', 'after', 'few', 'whom', 't', 'being', 'if', 'theirs', 'my',
             'against', 'a', 'by', 'doing', 'it', 'how', 'further', 'was', 'here', 'than'}


def dir_filter(file):
    return file.startswith(".")
# 检查 目录 是否以.开始


def file_filter(file):
    return not file.endswith(".")
# 检查 文件 是否以.结束，一般用来判断是否是某一文件类型


def files_from_dir(path, target_amount):
    files = []

    def dfs_dir(target_path):
        if len(files) == target_amount:
            return
        if os.path.isdir(target_path) and not dir_filter(target_path):  # 文件夹
            subs = os.listdir(target_path)
            for sub in subs:
                dfs_dir(os.path.join(target_path, sub))  # 当前文件夹拼接
                if len(files) == target_amount:
                    break
        elif os.path.isfile(target_path) and not file_filter(target_path):  # 文件
            files.append(target_path)
        else:
            print("skip " + target_path)

    dfs_dir(path)
    return files
# 深度优先搜索获得文件列表


def file_parser(file):
    with open(file, 'r') as f:
        c = []
        try:
            lines = f.readlines()
            # print(lines)
            reach_head = False
            seen = set()  # 无序不重复元素集
            for line in lines:
                if line.startswith('X-FileName'):
                    reach_head = True
                    continue
                # skip mail header
                if not reach_head:
                    continue
                # skip mail forward and appended mail
                if 'Forwarded by' in line:
                    continue
                if 'Original Message' in line:
                    continue
                if 'From:' in line:
                    continue
                if 'To:' in line:
                    continue
                if 'Cc:' in line:
                    continue
                if 'Sent:' in line:
                    continue
                if 'Subject:' in line:
                    continue
                if 'cc:' in line:
                    continue
                if 'subject:' in line:
                    continue
                if 'Subject:' in line:
                    continue
                if 'from:' in line:
                    continue
                # line = line.replace('\n',' ')
                line = re.sub(r"[^\s]*@[^\s]*", " ", line)  # 将无关紧要的关键字替换成空格
                line = re.sub(r"[^A-Za-z]", " ", line).lower()
                # print(line.split())

                # remove duplicate words
                tmp = line.split()
                line = []
                for l in tmp:
                    if len(l) >= 2 and l not in stopWords and l not in seen:
                        seen.add(l)
                        line.append(l)
                line = ' '.join(line)  # 以空格连接各个关键字
                if len(line) != 0:
                    c.append(line)
                    # print(line)
        except UnicodeDecodeError:
            print(file)
            return ''
        # c_lists = content.split()
        # content = ' '.join([c for c in c_lists if enDict.check(c)]) # check if is a word
    return ' '.join(c)
# 解析逐个文件


def get_corpus_from_dir(path, target_amount):
    fs = files_from_dir(path, target_amount + target_amount // 50)  # 此处整除50的作用？？
    print("geting corpus from files")
    cps = []
    skip_count = 0
    for i in range(len(fs)):
        content = file_parser(fs[i])
        # print("content")
        # print(content)
        if len(content) == 0:
            skip_count += 1
            continue
        cps.append(content)
    # print("skip:", skip_count)
    # print("total:", len(cps))
    return cps[:target_amount]
# 从目录获取关键字


# 获得1000个文件
# 获得关键字到文件的列表
def build_key_to_file_list(bv):
    Kw_File = {}
    for i, content_str in enumerate(bv):  # bv list
        content_list = content_str.split()
        for content in content_list:
            if content not in Kw_File:
                Kw_File[content] = [str(i).zfill(16)]  # build key(content) value(16 string)
            else:
                Kw_File[content].append(str(i).zfill(16))
    Kw_File_Use = {}
    kw_id_number = {}
    kw_prime = {}
    for kw in Kw_File:
        if len(kw) < 14:
            Kw_File_Use[kw] = Kw_File[kw]
    # count id number containing each keyword
    for kw in Kw_File_Use:
        kw_id_number[kw] = len(Kw_File_Use[kw])
    # map kw to primes
    prime = 2
    for kw in Kw_File_Use:
        prime = gmpy2.next_prime(prime)
        kw_prime[kw] = int(prime)
    return Kw_File_Use, kw_prime, kw_id_number


bv = get_corpus_from_dir("/home/mwang235/Downloads/maildir", file_amount)
(Kw_File_Use, kw_prime, kw_id_number) = build_key_to_file_list(bv)
print('Kw_File_Use', len(Kw_File_Use), Kw_File_Use)
print('kw_prime', len(kw_prime), kw_prime)
print('kw_id_number', len(kw_id_number), kw_id_number)


def count():
    fileSum = 0
    word = 0
    primeSum = 0
    for kw in Kw_File_Use:  # 统计关键字数量
        word = word + 1
        for j in Kw_File_Use[kw]:
            fileSum = fileSum + 1  # 统计每一个关键字对应文件数量
    for p in kw_prime:
        primeSum = primeSum + 1
    return word, fileSum, primeSum


f_Kw_File_Use=open('/home/mwang235/Dropbox/Code/DataSharing/Kw_File_Use.txt', 'wb')
pickle.dump(Kw_File_Use, f_Kw_File_Use, 0)  # 以文本的形式序列化对象，并将结果数据写入到文件对象中（可读性差）
f_Kw_File_Use.close()
# print(len(Kw_File_Use['john']))

f_kw_prime = open('/home/mwang235/Dropbox/Code/DataSharing/kw_prime.txt', 'wb')
pickle.dump(kw_prime, f_kw_prime, 0)
f_kw_prime.close()

print("word, file number", count())

#load 50 files ----> 1592 kw -----> 2959 id
#load 100 files ----> 2861 kw -----> 6790 id
#load 200 files ----> 4278 kw -----> 13682 id
#load 400 files ----> 7798 kw -----> 31845 id
#load 800 files ----> 12835 kw -----> 75852 id

