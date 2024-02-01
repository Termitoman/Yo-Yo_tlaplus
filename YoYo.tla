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

\* nodeState : Pour chaque node, son état actuel (Source, Sink, InteNodesediary, NotProcessed)
VARIABLE nodeState
------------------------------------------------------------
YYTypeOK == nodeState \in [Nodes -> {"Source", "Intermediary", "Sink", "NotProcessed"}]

\* INIT
YYInit == nodeState = [n \in Nodes |-> "NotProcessed"]

directEdgesAsSource(n) == TRUE

directEdgesAsIntermediary(n) == TRUE

directEdgesAsSink(n) == TRUE

isSource(n) == /\ \A m \in Nodes : (\E e \in Edges : (e = {n, m} \/ e = {m, n}) => (m > n)) \/ (\A e \in Edges : ~(n \in e /\ m \in e))
               /\ nodeState' = [nodeState EXCEPT ![n] = "Source"]
               /\ directEdgesAsSource(n)
    
isIntermediary(n) == /\ \E m \in Nodes : (\E e \in Edges : (e = {n, m} \/ e = {m, n}) /\ m > n)
                     /\ \E m \in Nodes : (\E e \in Edges : (e = {n, m} \/ e = {m, n}) /\ m < n)
                     /\ nodeState' = [nodeState EXCEPT ![n] = "Intermediary"]
                     /\ directEdgesAsIntermediary(n)

isSink(n) == /\ \A m \in Nodes : (\E e \in Edges : (e = {n, m} \/ e = {m, n}) => (m < n)) \/ (\A e \in Edges : ~(n \in e /\ m \in e))
             /\ nodeState' = [nodeState EXCEPT ![n] = "Sink"]
             /\ directEdgesAsSink(n)

PreProcess(n) == /\ nodeState[n] = "NotProcessed"
                 /\ \/ isSource(n)
                    \/ isIntermediary(n)
                    \/ isSink(n)

\* NEXT
YYNext == \E n \in Nodes : PreProcess(n)

====