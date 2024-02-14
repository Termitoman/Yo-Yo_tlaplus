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
YYTypeOK == 
    /\ nodeState \in [Nodes -> {"Source", "Intermediary", "Sink"}]
    /\ nodesEntering \in [Nodes -> SUBSET Nodes]
    /\ nodesLeaving \in [Nodes -> SUBSET Nodes]
    /\ msgs \in [Nodes -> SUBSET Messages]

\* Définit l'ensemble des nodes voisins d'un node
Neighbors(n) == {m \in Nodes : {m,n} \in Edges}

\* Initialisation des variables et préprocessing
\* On effectue le préprocessing de façon synchrone car cette phase n'est pas très intéressante
YYInit == 
    /\ nodesEntering = [n \in Nodes |-> { m \in Neighbors(n) : m < n}]
    /\ nodesLeaving = [n \in Nodes |-> { m \in Neighbors(n) : m > n}]
    /\ nodeState = [n \in Nodes |-> 
                    IF nodesEntering[n] = Neighbors(n) THEN "Sink"
                    ELSE IF nodesLeaving[n] = Neighbors(n) THEN "Source"
                    ELSE "Intermediary"]
    /\ msgs = [n \in Nodes |-> {}]


-------------------------------------------------------------

\* Minimum d'un set d'entiers
Min(set) == CHOOSE x \in set : \A y \in set : x <= y

\* Envoi des messages de source
\* Chaque source envoie un message contenant son ID à chaque node sortant
EnvoiIDSource(n) == 
    /\ nodeState[n] = "Source"
    /\ msgs' = [m \in Nodes |-> 
        IF m \in nodesLeaving[n] THEN msgs[m] \cup {[node |-> n, val |-> n]} ELSE msgs[m]]

\* Envoi des messages d'intermédiaire
\* Si l'intermédiaire à reçu un message de toutes ses entrées, il envoie un message contenant l'ID minimum à chaque node sortant
EnvoiIDIntermediary(n) == 
    /\ nodeState[n] = "Intermediary"
    /\ \A m \in nodesEntering[n] : \E msg \in msgs[n] : msg.node = m
    /\ msgs' = [m \in Nodes |-> 
        IF m \in nodesLeaving[n] THEN msgs[m] \cup {[node |-> n, val |-> Min({msg.val : msg \in msgs[n]})]} ELSE msgs[m]]

\* Envoi des messages de sink
\* Les sink ne font rien pour cette phase
EnvoiIDSink(n) == 
    /\ nodeState[n] = "Sink"
    /\ UNCHANGED msgs

\* Etape "Yo" comme décrit dans la page wikipedia
\* Cette étape ne se fait que si toutes les nodes ont fini l'étape de pré-traitement
\* Chaque source envoie un message contenant son ID à chaque node sortant
\* Chaque intermédiaire envoie un message contenant l'ID de la source (minimum entre tous les entrants) à chaque node sortant
\* Les sink ne font rien pour cette phase
YoPhase(n) == 
    /\  \/ EnvoiIDSource(n)
        \/ EnvoiIDIntermediary(n)
        \/ EnvoiIDSink(n)
    /\ UNCHANGED <<nodeState, nodesEntering, nodesLeaving>>

-------------------------------------------------------------

\* Vérifie que tous les sink ont reçus un message de toutes leurs entrées
SinksHaveReceived(n) == 
    \A node \in Nodes : nodeState[node] = "Sink" => \A m \in nodesEntering[node] : \E msg \in msgs[node] : msg.node = m

\* Envoi des messages de sink
\* Chaque sink envoie un message "YES" à la node entrante lui ayant envoyé un message avec la plus petite valeur et un message "NO" aux autres
SendYesNoSink(n) == 
    /\ nodeState[n] = "Sink"
    /\ msgs' = [m \in Nodes |-> 
        IF m \in nodesEntering[n] THEN msgs[m] \cup {[node |-> n, type |-> 
            IF LET minVal == Min({msg.val : msg \in msgs[n]}) IN minVal = msg.val 
            THEN "YES" ELSE "NO"]} ELSE msgs[m]]

\* Envoi du message "YES" et des messages "NO" d'un intermédiaire
IntermediaryYes(n) == 
    /\ \A m \in nodesLeaving[n] : \E msg \in msgs[n] : msg.node = m /\ msg.type = "YES"
    /\ msgs' = [m \in Nodes |-> 
        IF m \in nodesEntering[n] THEN msgs[m] \cup {[node |-> n, type |-> 
            IF LET minVal == Min({msg.val : msg \in msgs[n]}) IN minVal = msg.val 
            THEN "YES" ELSE "NO"]} ELSE msgs[m]]

\* Envoi des messages "NO" d'un intermédiaire
IntermediaryNo(n) == 
    /\ \E m \in nodesLeaving[n] : \E msg \in msgs[n] : msg.node = m /\ msg.type = "NO"
    /\ msgs' = [m \in Nodes |-> 
        IF m \in nodesEntering[n] THEN msgs[m] \cup {[node |-> n, type |-> "NO"]} ELSE msgs[m]]

\* Envoi des messages d'intermédiaire
\* Si l'intermédiaire à reçu un message de toutes ses sorties, si il à reçu que des "YES", il envoie un message "YES" à la node entrante lui ayant envoyé un message avec la plus petite valeur et un message "NO" aux autres, sinon il envoie "NO" à toutes ses entrées
SendYesNoIntermediary(n) == 
    /\ nodeState[n] = "Intermediary"
    /\ \A m \in nodesLeaving[n] : \E msg \in msgs[n] : msg.node = m
    /\  \/ IntermediaryYes(n)
        \/ IntermediaryNo(n)

\* Envoi des messages "YES" et "NO" d'une source
\* Les sources ne font rien pour cette phase
SendYesNoSource(n) == 
    /\ nodeState[n] = "Source"
    /\ UNCHANGED msgs

\* Etape "-Yo" comme décrit dans la page wikipedia
\* Cette étape ne se fait que si tous les sink ont reçus un message de toutes leurs entrées
\* Chaque sink envoie un message "YES" à la node entrante ayant la plus petite valeur et un message "NO" aux autres
\* Chaque intermédiaire, quand il à reçu un message de toutes ses sorties, envoie un message "YES" à la node entrante ayant valeur correspondante et un message "NO" aux autres
\* Les sources ne font rien pour cette phase
DashYoPhase(n) == 
    /\ SinksHaveReceived(n)
    /\  \/ SendYesNoSink(n)
        \/ SendYesNoIntermediary(n)
        \/ SendYesNoSource(n)
    /\ UNCHANGED <<nodeState, nodesEntering, nodesLeaving>>

-------------------------------------------------------------

\* Vérifie que toutes les sources ont reçus un message de toutes leurs sorties
SourcesHaveReceived(n) == \A node \in Nodes : nodeState[node] = "Source" => \A m \in nodesLeaving[node] : \E msg \in msgs[node] : msg.node = m

\* Etape de restructuration pour les sources
\* Chaque source qui n'a reçu que des messages "NO" devient un sink
\* Chaque source qui a reçu au moins un message "NO" et un message "YES" devient un intermédiaire
\* Chaque source qui a reçu que des messages "YES" reste une source
\* Les nodes entrantes et sortantes sont recalculées
SourceRestructuration(n) == 
    /\ nodeState[n] = "Source"
    /\  \/  /\ \A m \in nodesLeaving[n] : \E msg \in msgs[n] : msg.node = m /\ msg.type # "NO"
            /\ UNCHANGED << nodeState, nodesEntering, nodesLeaving >>
        \/  /\ \A m \in nodesLeaving[n] : \E msg \in msgs[n] : msg.node = m /\ msg.type # "YES"
            /\ nodeState' = [nodeState EXCEPT ![n] = "Sink"]
            /\ nodesEntering' = [nodesEntering EXCEPT ![n] = nodesLeaving[n]]
            /\ nodesLeaving' = [nodesLeaving EXCEPT ![n] = {}]
        \/  /\ \E m \in nodesLeaving[n] : \E msg \in msgs[n] : msg.node = m /\ msg.type = "YES"
            /\ \E m \in nodesLeaving[n] : \E msg \in msgs[n] : msg.node = m /\ msg.type = "NO"
            /\ nodeState' = [nodeState EXCEPT ![n] = "Intermediary"]
            /\ LET yesNodes == {msg.val : msg \in {m \in msgs[n] : m.type = "YES"}}
                IN (/\ nodesEntering' = [nodesEntering EXCEPT ![n] = nodesLeaving[n] \ yesNodes]
                    /\ nodesLeaving' = [nodesLeaving EXCEPT ![n] = yesNodes])

\* Etape de restructuration pour les intermédiaires
\* Chaque intermédiaire qui à reçu que des NO echange ses entrées et sorties
\* Chaque intermédiaire qui à reçu un message YES échange toutes ses entrées et sorties ayant transporté un message NO
IntermediaryRestructuration(n) ==
    /\ nodeState[n] = "Intermediary"
    /\  \/  /\ \E m \in nodesEntering[n] : \E msg \in msgs[m] : msg.node = n /\ msg.type = "YES"
            /\ LET noNodes == {msg.val : msg \in {m \in msgs[n] : m.type = "NO"}} \cup {m \in nodesEntering[n] : \E msg \in msgs[m] : msg.node = n /\ msg.type = "NO"}
                IN (/\ nodesEntering' = [nodesEntering EXCEPT ![n] = (nodesEntering[n] \ noNodes) \cup (nodesLeaving[n] \intersect noNodes)]
                    /\ nodesLeaving' = [nodesLeaving EXCEPT ![n] = (nodesLeaving[n] \ noNodes) \cup (nodesEntering[n] \intersect noNodes)])
        \/  /\ \A m \in nodesEntering[n] : \E msg \in msgs[m] : msg.node = n /\ msg.type = "NO"
            /\ \A m \in nodesLeaving[n] : \E msg \in msgs[n] : msg.node = m /\ msg.type = "NO"
            /\ nodesEntering' = [nodesEntering EXCEPT ![n] = nodesLeaving[n]]
            /\ nodesLeaving' = [nodesLeaving EXCEPT ![n] = nodesEntering[n]]
    /\ UNCHANGED nodeState

\* Etape de restructuration pour les sinks
\* Chaque sink qui a plus d'1 node entrante devient un intermédiaire, toutes les nodes avec un message NO passent en nodes sortante
\* Chaque sink qui a 1 seule node entrante reste un sink
SinkRestructuration(n) == 
    /\ nodeState[n] = "Sink"
    /\  \/  /\ Cardinality(nodesEntering[n]) > 1
            /\ nodeState' = [nodeState EXCEPT ![n] = "Intermediary"]
            /\ LET noNodes == {m \in nodesEntering[n] : \E msg \in msgs[m] : msg.node = n /\ msg.type = "NO"}
                IN (/\ nodesEntering' = [nodesEntering EXCEPT ![n] = nodesEntering[n] \ noNodes]
                    /\ nodesLeaving' = [nodesLeaving EXCEPT ![n] = noNodes])
        \/  /\ Cardinality(nodesEntering[n]) = 1
            /\ UNCHANGED << nodeState, nodesLeaving, nodesEntering >>

\* Etape de restructuration comme décrit dans la page wikipedia
\* Cette phase ne peut se faire que si toutes les sources ont reçut un message de toutes leurs sorties
\* Chaque source qui a reçu un message "NO" devient un sink ou un intermédiaire
\* Chaque sink qui a plus d'1 node entrante devient un intermédiaire
\* Les intermédiaires restent des intermédiaires
\* Chaque arête qui a reçu un message "NO" est inversée, ce qui implique que chaque node change ses entrées et sorties en consequence
Restructuration(n) == 
    /\ SourcesHaveReceived(n)
    /\  \/ SinkRestructuration(n)
        \/ IntermediaryRestructuration(n)
        \/ SourceRestructuration(n)
    /\ UNCHANGED msgs

-------------------------------------------------------------

\* Définition du prochain état
YYNext == \E n \in Nodes : YoPhase(n) \/ DashYoPhase(n) \/ Restructuration(n)

=============================================================