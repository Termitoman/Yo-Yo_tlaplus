\* Module qui abstrait l'algorithme d'élection de leader Yo-Yo.
\* Ecrit par Ludovic Yvoz pour le cours de Vérification Algorithmique

------------------------ MODULE YoYo ------------------------
EXTENDS TLC, Integers, FiniteSets

\* Nodes : l'ensemble des nodes du graphe
\* Edges : l'ensemble des arêtes du graphe
CONSTANT Nodes, Edges

\* Vérifie que les données en entrée sont correctes
ASSUME  /\ Nodes \subseteq Int
        /\ Nodes # {} 
        /\ Edges \subseteq SUBSET Nodes
        /\ \A e \in Edges : Cardinality(e) = 2  \* en particulier cela exclut des auto-boucles
        \*/\ \A n \in Nodes : \E m \in Nodes : \E e \in Edges : ~(n = m) /\ (\E x \in e : \E y \in e : ~(x = y) /\ x = n /\ y = m)

\* nodeState : Pour chaque node, son état actuel (Source, Sink, Intermediary, NotProcessed)
\* nodesEntering : Pour chaque node, l'ensemble des nodes qui entrent dans ce node (arêtes orientées vers ce node)
\* nodesLeaving : Pour chaque node, l'ensemble des nodes qui sortent de ce node (arêtes orientées depuis ce node)
VARIABLE nodeState, nodesEntering, nodesLeaving

-------------------------------------------------------------

\* Vérifie que les variables restent dans un état correct
YYTypeOK == /\ nodeState \in [Nodes -> {"Source", "Intermediary", "Sink", "NotProcessed"}]
            /\ nodesEntering \in [Nodes -> SUBSET Nodes]
            /\ nodesLeaving \in [Nodes -> SUBSET Nodes]

\* Initialisation des variables
YYInit == /\ nodeState = [n \in Nodes |-> "NotProcessed"]
          /\ nodesEntering = [n \in Nodes |-> {}]
          /\ nodesLeaving = [n \in Nodes |-> {}]

-------------------------------------------------------------

\* On dirige les arêtes d'une source lors du préprocessing
directEdgesAsSource(n) == /\ nodesLeaving' = [nodesLeaving EXCEPT ![n] = {m \in Nodes : \E e \in Edges : (e = {n, m} \/ e = {m, n})}]
                          /\ UNCHANGED nodesEntering

\* On dirige les arêtes d'un intermédiaire lors du préprocessing
directEdgesAsIntermediary(n) == /\ nodesLeaving' = [nodesLeaving EXCEPT ![n] = {m \in Nodes : (m > n) /\ \E e \in Edges : (e = {n, m} \/ e = {m, n})}]
                                /\ nodesEntering' = [nodesEntering EXCEPT ![n] = {m \in Nodes : (m < n) /\ \E e \in Edges : (e = {n, m} \/ e = {m, n})}]

\* On dirige les arêtes d'un sink lors du préprocessing
directEdgesAsSink(n) == /\ nodesEntering' = [nodesEntering EXCEPT ![n] = {m \in Nodes : \E e \in Edges : (e = {n, m} \/ e = {m, n})}]
                        /\ UNCHANGED nodesLeaving

\* On définit la node comme source si elle n'a pas de node entrant
Source(n) == /\ (\A m \in Nodes : (\E e \in Edges : (e = {n, m} \/ e = {m, n}) => (m > n)) \/ (\A e \in Edges : ~(n \in e /\ m \in e)))
             /\ nodeState' = [nodeState EXCEPT ![n] = "Source"]
             /\ directEdgesAsSource(n)

\* On définit la node comme intermédiaire si elle a des nodes entrants et sortants
Intermediary(n) == /\ \E m \in Nodes : (\E e \in Edges : (e = {n, m} \/ e = {m, n}) /\ m > n)
                   /\ \E m \in Nodes : (\E e \in Edges : (e = {n, m} \/ e = {m, n}) /\ m < n)
                   /\ nodeState' = [nodeState EXCEPT ![n] = "Intermediary"]
                   /\ directEdgesAsIntermediary(n)

\* On définit la node comme sink si elle n'a pas de node sortant
Sink(n) == /\ (\A m \in Nodes : (\E e \in Edges : (e = {n, m} \/ e = {m, n}) => (m < n)) \/ (\A e \in Edges : ~(n \in e /\ m \in e)))
           /\ nodeState' = [nodeState EXCEPT ![n] = "Sink"]
           /\ directEdgesAsSink(n)

\* Etape de pré-traitement comme décrit dans la page wikipedia
\* Chaque node passe de l'état NotProcessed à l'état Source, Sink ou Intermediary
\* Chaque arête est orientée de la source vers le sink
PreProcess(n) == /\ nodeState[n] = "NotProcessed"
                 /\ \/ Source(n)
                    \/ Intermediary(n)
                    \/ Sink(n)

-------------------------------------------------------------


\* Définition du prochain état
YYNext == \E n \in Nodes : PreProcess(n)

=============================================================