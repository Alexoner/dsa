# Three-Bucket(Water Pouring) Problem

# Problem Description
In this scenario, there are an 8-liter bucket filled with water and empty 3-liter and 5-liter buckets. You solve the puzzle by using the three buckets to divide the 8 liters of water into two equal parts of 4 liters.

## Solution
The problem can be turned into a maze if one denotes "position" in the maze by the contents of the three buckets in fixed order, with the problem being to get from "8-0-0" - that is, 8 pints in the biggest bucket, with the others empty, to "4-4-0" - four pints in the 8 and 5-pint buckets, the other one empty. Ian Stewart at Warwick has shown that "DEPTH-FIRST SEARCH" can solve this maze problem.

## code
../alg/search/uninformed/depthFirstSearch/threeBucket.py
