---- MODULE MCYoYo ----
EXTENDS Integers

CONSTANT NbNodes

Nodes == 1 .. NbNodes
Edges == { {1,3}, {2,3} }

VARIABLE nodeState, nodesEntering, nodesLeaving, msgs, phase

INSTANCE YoYo 
=======================