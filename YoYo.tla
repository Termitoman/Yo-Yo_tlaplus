\* Module qui abstrait l'algorithme d'élection de leader Yo-Yo.
\* Ecrit par Ludovic Yvoz pour le cours de Vérification Algorithmique

---- MODULE YoYo ----
EXTENDS TLC, Integers, FiniteSets

CONSTANT Nodes, Edges

\* Déclaration des constantes (nombre de noeuds, liste des id (entiers uniques) des noeuds, liste des arêtes)
ASSUME  /\ Nodes \subseteq Int
        /\ Nodes # {} 
        /\ Edges \subseteq SUBSET Nodes
        /\ \A e \in Edges : Cardinality(e) = 2  \* en particulier cela exclut des auto-boucles
        \*/\ \A n \in Nodes : \E m \in Nodes : \E e \in Edges : ~(n = m) /\ (\E x \in e : \E y \in e : ~(x = y) /\ x = n /\ y = m)

VARIABLE a

\* INIT
YYInit == a = 0

\* NEXT
YYNext == a' = a

====