#!python
# -*- coding: utf-8 -*-

"""
输入
2个manifest文件，一个gt结果，一个infer结果，通过相同audio_filepath字段关联
如果一个音频只在gt中出现或infer中出现，可以忽略。
例子
Input
{"audio_filepath": "2030-3740.wav", "text": "您好很高兴为您服务",...}
{"audio_filepath": "4510-9440.wav", "text": "我想问一下就是三块钱你要有那个是限时的对吧",...}
Output
<meta charset="UTF-8">
<span><strong>黑色： 一致，红色：不同</strong></span>
<br><br>
<span><strong>audio: ./datasets/ChinaMobile_CHN.v3/data/20170630_2660_15912864261_49S_0833116-10350-16390.wav </strong></span>
<br><table border="1">

<tr>
<td><span><strong>GT:</strong></span></td>
<td><span style="color: Red";">对</span><span style="color: Black";">当天开立即生效可以用到当天晚上十二点生效之前超出的流量不能抵扣</span></td>
</tr>

<tr>
<td><span><strong>infer:</strong></span></td>
<td><span style="color: Red";">在</span><span style="color: Black";">当天开立即生效可以用到当天晚上十二点生效之前超出的流量不能抵扣</span></td>
</tr>
</table>

<span><strong> duration:6.04</strong></span>
<br><br>

<span><strong>audio: ./datasets/ChinaMobile_CHN.v3/data/20170630_2660_15912864261_49S_0833116-17340-19300.wav </strong></span>
<br><table border="1">

<tr>
<td><span><strong>GT:</strong></span></td>
<td><span style="color: Black";">好了好了</span><span style="color: Red";">定一个</span><span style="color: Black";">现在订的</span></td>
</tr>

<tr>
<td><span><strong>infer:</strong></span></td>
<td><span style="color: Black";">好了好了</span><span style="color: Red";">并到</span><span style="color: Black";">现在订的</span></td>
</tr>
</table>

<span><strong> duration:1.96</strong></span>
<br><br>

<span><strong>audio: ./datasets/ChinaMobile_CHN.v3/data/20170630_2660_15912864261_49S_0833116-2030-3740.wav </strong></span>
<br><table border="1">

<tr>
<td><span><strong>GT:</strong></span></td>
<td><span style="color: Black";">您好很高兴为您服务</span></td>
</tr>

<tr>
<td><span><strong>infer:</strong></span></td>
<td><span style="color: Black";">您好很高兴为您服务</span></td>
</tr>
</table>
效果图


要求
python脚本
符合代码规范、脚本规范
使用脚本规范中的标准脚本模板
数据
具体见：python课程-part3-题目六
问题
最近刚刚训练了一个语音识别的模型，只通过性能指标可能无法完全了解模型的情况，需要进行更细致的错误分析。
目前已知测试集中的每段音频的gt和infer结果。需要将每段音频的gt和infer结果做对比，diff的地方标红，最后生成一个网页将所有比对结果显示出来。
如何定义diff：先求出gt和infer的最长公共子序列，其他的部分都认为是diff的
输出	生成的debug网页


"""

import os
import argparse
import logging
from multiprocessing import Pool
import subprocess
import pathlib
from functools import partial
import re
import json
from collections import Counter

from PIL import Image, ImageDraw
import pandas as pd
import matplotlib.pyplot as plt

def create_logger(logger_name,
                  log_format=None,
                  log_level=logging.INFO,
                  log_path=None):
    logger = logging.getLogger(logger_name)
    # assert (len(logger.handlers) == 0)
    logger.setLevel(log_level)
    if log_path is None:
        handler = logging.StreamHandler()
    else:
        os.stat(os.path.dirname(os.path.abspath(log_path)))
        handler = logging.FileHandler(log_path)
    handler.setLevel(log_level)
    if log_format is not None:
        formatter = logging.Formatter(log_format)
        handler.setFormatter(formatter)
    logger.addHandler(handler)

    return logger

logger = create_logger(
    logger_name='template',
    log_format='[%(asctime)s %(name)-13s %(levelname)s %(process)d %(thread)d \
    %(filename)s:%(lineno)-5d] %(message)s',
    log_level=logging.INFO)

parser = argparse.ArgumentParser()
parser.add_argument("--input", default="../../data/nlp/", help="input directory")
parser.add_argument("--output", default="/tmp/dsa/output/")
args = parser.parse_args()

def lcs(x, y):
    print('diff x and y: ', x, ' vs ',  y)
    m, n  = len(x), len(y)
    dp = [[0 for i in range(n + 1)] for _ in range(m + 1)]
    for i in range(1, m + 1):
        for j in range(1, n + 1):
            if x[i - 1] == y[j - 1]:
                dp[i][j] = dp[i - 1][j - 1] + 1
            else:
                dp[i][j] = max(dp[i][j-1], dp[i-1][j])
    matches = []
    from pprint import pprint
    print(dp)
    l = dp[m][n]
    i, j = m, n
    while i > 0 and j > 0:
    # for i in reversed(range(1, m + 1)):
        # for j in reversed(range(1, n + 1)):
            if x[i-1] == y[j-1]:
                matches.append((i, j))
                i -= 1
                j -= 1
            elif dp[i-1][j] >= dp[i][j-1]:
                i -= 1
            else:
                j -= 1

    # print(matches)
    return matches

def tag(flag, text, matchSet, f):
    f.write(f'''

<tr>
<td><span><strong>{flag}:</strong></span></td>

<td>
        ''') # literal string interpolation in Python

    i = 0
# <span style="color: Red";">%s</span>
# <span style="color: Black";">%s</span>
    while i < len(text):
        j = i
        if j + 1 in matchSet:
            f.write('<span style="color: Black";>')
            while j + 1 in matchSet and j < len(text):
                f.write(text[j])
                j += 1
            f.write('</span>')
        else:
            f.write('<span style="color: Red";>')
            while j + 1 not in matchSet and j < len(text):
                f.write(text[j])
                j += 1
            f.write('</span>')
        i = j

    f.write('''</td>
            </tr>
            ''')



def diff(inputPath, outputPath):
    gtPath = inputPath + "/manifest.gt"
    inferPath = inputPath + "/manifest.infer"

    # outputManifestPath = outputPath + "/manifest"
    outputHtmlPath = outputPath + "/diff.html"
    outputJsonPath = outputPath + "input.json"
    pathlib.Path(outputHtmlPath).parent.mkdir(parents=True, exist_ok=True)

    gtObjs = {} #
    inferObjs = {} #

    with open(gtPath, "r+") as f:
        for line in f:
            if not line:
                continue
            obj = json.loads(line)
            gtObjs[obj['audio_filepath']] = obj

    with open(inferPath, "r+") as f:
        for line in f:
            if not line:
                continue
            obj = json.loads(line)
            inferObjs[obj['audio_filepath']] = obj

    with open(outputHtmlPath, "w") as f:
        f.write('''
<meta charset="UTF-8">
<span><strong>黑色： 一致，红色：不同</strong></span>
<br><br>
                ''')

    outputJsonObj = []
    it = 0
    for fp, inferObj in inferObjs.items():
        # if it >= 100:
            # break
        it += 1
        if fp not in gtObjs:
            continue
        gtObj = gtObjs[fp]
        # TODO: longest common subsequence
        x, y = gtObj['text'], inferObj['text']
        matches = lcs(x, y)
        xIndices = {x[0] for x in matches }
        yIndices = {x[1] for x in matches }

        audioPath = fp
        duration = inferObj['duration']

        with open(outputHtmlPath, "a") as f:
            f.write(f'''

<span><strong>audio: {audioPath} </strong></span>
<br><table border="1">
                    ''')
            tag('GT', x, xIndices, f)
            tag('infer', y, yIndices, f)

            f.write(f'''
                    </table>

<span><strong> duration:{duration}</strong></span>
<br><br>
                    ''')
        outputJsonObj.append({
            'gt': x,
            'infer': y,
            'file_path': fp,
        })

    with open(outputJsonPath, "w") as f:
        json.dump(outputJsonObj, f, ensure_ascii=False, indent=4)


if __name__ == '__main__':
    diff(args.input, args.output)
