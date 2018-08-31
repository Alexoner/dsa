#!/usr/bin/env python
# -*- coding: utf-8 -*-

"""
Template for python application.

"""

import argparse
import logging
from logging.config import fileConfig
import requests

fileConfig("./logging/logging.conf")
logger = logging.getLogger(__name__)

def test_log():
    logger.info("this is info")
    logger.warning("this is warning")
    logger.debug("this is debug")
    logger.error("this is error")
    logger.fatal("this is fatal")
    logger.critical("this is critical")
    def f():
        try:
            requests.get("this is not an url at all")
        except Exception as e:
            logger.exception(e)
            # logger.error(f"input is emtty", exc_info=True)
            # logger.error("input must be empty")
        pass

    f()
    logger.info("self test done!")

def test_sum(l):
    logger.info(f"l: {l}, sum: {sum(l)}")

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='python application template')
    # parser.add_argument('integers', metavar='N', type=int, nargs='+',
                    # help='an integer for the accumulator', default=[0])
    parser.add_argument('integers', metavar='N', type=int, nargs='*',
                    help='an integer for the accumulator', default=[0])

    parser.add_argument('--sum', dest='accumulate', action='store_const',
                    const=sum, default=max,
                    help='sum the integers (default: find the max)')
    args = parser.parse_args()
    logger.info(f"args.integers: {args.integers}")
    test_sum(args.integers)
    # print(args.accumulate(args.integers))
    test_log()
