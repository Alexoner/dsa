/*
 * Orienteering
 *
 * We are planning an orienteering game.
 *
 * The aim of this game is to arrive at the goal (G) from the start (S) with the
 *shortest distance.
 *
 * However, the players have to pass all the checkpoints (@) on the map.
 *
 * An orienteering map is to be given in the following format.
 *
 * ------------
 * | ######## |
 * | #@....G# |
 * | ##.##@## |
 * | #..@..S# |
 * | #@.....# |
 * | ######## |
 * ------------
 *
 *  In this problem, an orienteering map is to be given.
 *
 * Calculate the minimum distance from the start to the goal with passing
 *  all the checkpoints.
 *
 *
 * A map consists of 5 characters as following.
 * You can assume that the map does not contain any invalid characters and
 *
 * the map has exactly one start symbol 'S' and exactly one goal symbol 'G'.

 * 'S' means the orienteering start.
 * 'G' means the orienteering goal.
 * '@' means an orienteering checkpoint.
 * '.' means an opened-block that players can pass.
 * '#' means a closed-block that players cannot pass.
 * It is allowed to move only by one step vertically or horizontally (up,
 * down, left, or right) to the
 * next block.
 * Other types of movements, such as moving diagonally (left up, right up,
 * left down and right down) and skipping one or more blocks, are NOT
 * permitted.
 * You MUST NOT get out of the map.
 * Distance is to be defined as the number of movements to the different
 * blocks.
 * You CAN pass opened-blocks, checkpoints, the start, and the goal more
 * than once if necessary.
 * You can assume that parameters satisfy following conditions.
 *
 * 1 <= width <= 100
 * 1 <= height <= 100
 * The maximum number of checkpoints is 18.
 *
 * Return -1 if given arguments do not satisfy specifications, or players
 * cannot arrive at the goal from the start by passing all the checkpoints.
 *
 *
 *
 *
 * Input
 *
The input is to be given in the following format, from the standard input.
 W H
 Row1
 Row2
 ...
 RowH
The first row is to describe the width and the height of the orienteering
map, sectioned by a space.
From the second row, map information is to be given for exactly the same
number of rows as the height.
Each row contains exactly the same number of letters as the width.



 * Output
 * Output the standard output,and put a return.
 */
