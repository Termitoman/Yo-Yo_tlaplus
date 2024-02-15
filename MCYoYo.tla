---- MODULE MCYoYo ----
EXTENDS Integers

CONSTANT NbNodes

Nodes == 1 .. NbNodes
Edges == { {1, 2}, {1, 4}, {2, 4}, {2, 7}, {3, 4}, {3, 6}, {5, 6}, {5, 7}, {5, 9}, {6, 8}, {6, 9}, {7, 8} }

VARIABLE nodeState, nodesEntering, nodesLeaving, msgs, phase

INSTANCE YoYo 
=======================