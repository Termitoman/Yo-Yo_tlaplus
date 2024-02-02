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
\* msgs : Pour chaque node, l'ensemble des messages qu'il a reçu
VARIABLE nodeState, nodesEntering, nodesLeaving, msgs

\* Messages : L'ensemble des messages possibles entre nodes
Messages == [node : Nodes, val : Nodes]  \cup  [node : Nodes, type : {"YES", "NO"}]

-------------------------------------------------------------

\* Vérifie que les variables restent dans un état correct
YYTypeOK == /\ nodeState \in [Nodes -> {"Source", "Intermediary", "Sink", "NotProcessed"}]
            /\ nodesEntering \in [Nodes -> SUBSET Nodes]
            /\ nodesLeaving \in [Nodes -> SUBSET Nodes]
            /\ msgs \in [Nodes -> SUBSET Messages]

\* Initialisation des variables
YYInit == /\ nodeState = [n \in Nodes |-> "NotProcessed"]
          /\ nodesEntering = [n \in Nodes |-> {}]
          /\ nodesLeaving = [n \in Nodes |-> {}]
          /\ msgs = [node \in Nodes |-> {}]

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
                 /\ UNCHANGED msgs

-------------------------------------------------------------

\* Minimum d'un set d'entiers
Min(set) == CHOOSE x \in set : \A y \in set : x <= y

\* Envoi des messages de source
\* Chaque source envoie un message contenant son ID à chaque node sortant
EnvoiIDSource(n) == /\ nodeState[n] = "Source"
                    /\ \A m \in nodesLeaving[n] : msgs' = [msgs EXCEPT ![m] = msgs[m] \cup {[node |-> n, val |-> n]}]

\* Envoi des messages d'intermédiaire
\* Si l'intermédiaire à reçu un message de toutes ses entrées, il envoie un message contenant l'ID minimum à chaque node sortant
EnvoiIDIntermediary(n) == /\ nodeState[n] = "Intermediary"
                          /\ \A m \in nodesEntering[n] : \E msg \in msgs[n] : msg.node = m
                          /\ \A m \in nodesLeaving[n] : msgs' = [msgs EXCEPT ![m] = msgs[m] \cup {[node |-> n, val |-> Min({msg.type : msg \in msgs[n]})]}]

\* Envoi des messages de sink
\* Les sink ne font rien pour cette phase
EnvoiIDSink(n) == /\ nodeState[n] = "Sink"
                  /\ UNCHANGED msgs

\* Etape "Yo" comme décrit dans la page wikipedia
\* Cette étape ne se fait que si toutes les nodes ont fini l'étape de pré-traitement
\* Chaque source envoie un message contenant son ID à chaque node sortant
\* Chaque intermédiaire envoie un message contenant l'ID de la source (minimum entre tous les entrants) à chaque node sortant
\* Les sink ne font rien pour cette phase
YoPhase(n) == /\ \A node \in Nodes : nodeState[node] # "NotProcessed"
              /\ \/ EnvoiIDSource(n)
                 \/ EnvoiIDIntermediary(n)
                 \/ EnvoiIDSink(n)
              /\ UNCHANGED <<nodeState, nodesEntering, nodesLeaving>>

-------------------------------------------------------------


\* Définition du prochain état
YYNext == \E n \in Nodes : PreProcess(n) \/ YoPhase(n) \/ DashYoPhase(n)

=============================================================