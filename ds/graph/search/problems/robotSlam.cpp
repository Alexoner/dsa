/**
 *

There is a robot in a room. The initial location of the robot is unknown. The shape or area of the room is unknown.
You have a remote that could walk the robot into any of the four directions - up, left, down or right.
Here is the move method: boolean move(int direction), direction: 0, 1, 2, 3. If the robot hits the wall, the method returns false.
Otherwise returns true and the robot moves on to the direction given.
Find out the area of the room.


e.g.
X
XXX X
XXXXX 'X' marks the floor plan of the room.

A room like such has an area of 10.

Origin: https://careercup.com/question?id=4902310128910336
==============================================================================================
SOLUTION

This problem can be treated as a GRAPH, where vertices are points in the room, and edges are
possible move directions determined by a 'move' function.

The shape of room is unknown. It doesn't matter, we do it brute force.
Explore every point in the room.

The initial location is unknown, doesn't matter, we build coordinate system by ourself.
Let the initial location be (0, 0).


Depth first search, since a robot can't be multiple places at the same time, in this scenario.
So the idea is to do backtracking depth first search on this graph.

##############################################################################################
SIMILAR QUESTIONS
Mininature of SLAM(simultaneous localization and mapping)
扫地机器人算法


 */
