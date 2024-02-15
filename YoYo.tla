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
\* phase : Pour chaque node, la phase qu'il va effectuer (Yo, -Yo)
VARIABLE nodeState, nodesEntering, nodesLeaving, msgs, phase

\* Messages : L'ensemble des messages possibles entre nodes
Messages == [node : Nodes, val : Nodes, phase : {"Yo"}]  \cup  [node : Nodes, type : {"YES", "NO"}, phase : {"-Yo"}]

-------------------------------------------------------------

\* Vérifie que les variables restent dans un état correct
YYTypeOK == 
    /\ nodeState \in [Nodes -> {"Source", "Intermediary", "Sink"}]
    /\ nodesEntering \in [Nodes -> SUBSET Nodes]
    /\ nodesLeaving \in [Nodes -> SUBSET Nodes]
    /\ msgs \in [Nodes -> SUBSET Messages]
    /\ phase \in [Nodes -> {"Yo", "-Yo"}]

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
    /\ phase = [n \in Nodes |-> "Yo"]

\* Définition d'invariants controlant l'état des variables

YYEnteringOK == \A n \in Nodes : nodesEntering[n] \subseteq Neighbors(n)

YYLeavingOK == \A n \in Nodes : nodesLeaving[n] \subseteq Neighbors(n)

YYStateOK == \A n \in Nodes : 
    /\ nodeState[n] = "Source" => nodesEntering[n] = {}
    /\ nodeState[n] = "Sink" => nodesLeaving[n] = {}
    /\ nodeState[n] = "Intermediary" => nodesEntering[n] # {} /\ nodesLeaving[n] # {}

YYMsgsOK == \A n \in Nodes : \A msg \in msgs[n] : 
    /\ msg.node \in Neighbors(n)
    /\ msg.phase = "Yo" => msg.val \in Nodes

\* Définition d'un invariant faux quand l'algorithme termine pour regarder l'éxécution de l'algorithme
\* YYFalse == Cardinality({n \in Nodes : nodeState[n] = "Source"}) > 1

-------------------------------------------------------------

\* Minimum d'un set d'entiers
Min(set) == CHOOSE x \in set : \A y \in set : x <= y

\* Envoi des messages de source
\* Chaque source envoie un message contenant son ID à chaque node sortant
\* Cette phase ne s'exécute que si la source est en phase "Yo"
EnvoiIDSource(n) == 
    /\ nodeState[n] = "Source"
    /\ phase[n] = "Yo"
    /\ msgs' = [m \in Nodes |-> 
        IF m \in nodesLeaving[n] THEN msgs[m] \cup {[node |-> n, val |-> n, phase |-> "Yo"]} ELSE msgs[m]]
    /\ phase' = [phase EXCEPT ![n] = "-Yo"]

\* Envoi des messages d'intermédiaire et gestion des sink
\* Si l'intermédiaire à reçu un message de toutes ses entrées, il envoie un message contenant l'ID minimum à chaque node sortant
\* Les sinks ne font rien à part passer à la prochaine phase
\* Cette phase ne s'éxécute que si la node à reçu un message de toutes ses entrées et que la phase est "Yo"
YoPhaseIntermediarySink(n) == 
    /\ nodeState[n] \in {"Intermediary", "Sink"}
    /\ phase[n] = "Yo"
    /\ \A m \in nodesEntering[n] : \E msg \in msgs[n] : msg.node = m /\ msg.phase = "Yo"
    /\ msgs' = [m \in Nodes |-> 
        IF m \in nodesLeaving[n] THEN msgs[m] \cup {[node |-> n, val |-> 
            LET msgsYoPhase == {msg \in msgs[n] : msg.phase = "Yo"}
            IN (Min({msg.val : msg \in msgsYoPhase})), 
        phase |-> "Yo"]} ELSE msgs[m]]
    /\ phase' = [phase EXCEPT ![n] = "-Yo"]

\* Etape "Yo" comme décrit dans la page wikipedia
\* Cette étape ne se fait que si toutes les nodes ont fini l'étape de pré-traitement
\* Chaque source envoie un message contenant son ID à chaque node sortant
\* Chaque intermédiaire envoie un message contenant l'ID de la source (minimum entre tous les entrants) à chaque node sortant
\* Les sink ne font rien pour cette phase
YoPhase(n) == 
    /\  \/ EnvoiIDSource(n)
        \/ YoPhaseIntermediarySink(n)
    /\ UNCHANGED <<nodeState, nodesEntering, nodesLeaving>>

-------------------------------------------------------------

\* opérateur qui retourne l'état d'un noeud selon ses entrée et sorties
ComputeState(nEnter, nLeave) == 
    IF nEnter = {} THEN "Source"
    ELSE IF nLeave = {} THEN "Sink"
    ELSE "Intermediary"

\* Envoi des messages de sink
\* Le sink n'effectue la phase que si il à reçu un message de toutes ses entrées
\* Chaque sink envoie un message "YES" à la node entrante lui ayant envoyé un message avec la plus petite valeur et un message "NO" aux autres
\* Chaque sink inverse les arêtes qui ont transporté un message "NO"
\* Chaque sink nettoie ses messages quand il à fini
DashYoSink(n) == 
    /\ nodeState[n] = "Sink"
    /\ phase[n] = "-Yo"
    /\ \A m \in nodesEntering[n] : \E msg \in msgs[n] : msg.node = m /\ msg.phase = "Yo"
    /\ LET minVal == Min({msg.val : msg \in msgs[n]}) 
        IN (LET notMinNodes == {m \in nodesEntering[n] : \E msg \in msgs[n] : msg.node = m /\ msg.val # minVal} 
            IN (/\ msgs' = [m \in Nodes |-> 
                    IF m \in notMinNodes THEN msgs[m] \cup {[node |-> n, type |-> "NO", phase |-> "-Yo"]} 
                    ELSE IF m \in nodesEntering[n] THEN msgs[m] \cup {[node |-> n, type |-> "YES", phase |-> "-Yo"]} 
                        ELSE IF m = n THEN {} 
                            ELSE msgs[m]]
                /\ nodesEntering' = [nodesEntering EXCEPT ![n] = nodesEntering[n] \ notMinNodes]
                /\ nodesLeaving' = [nodesLeaving EXCEPT ![n] = notMinNodes]
                /\ nodeState' = [nodeState EXCEPT ![n] = ComputeState(nodesEntering'[n], nodesLeaving'[n])]))
    /\ phase' = [phase EXCEPT ![n] = "Yo"]

\* Envoi des messages d'intermédiaire
\* L'intérmédiaire n'effectue la phase que si il à reçu un message de toutes ses sorties
\* Chaque intermédiaire ayant reçu un "NO" envoie un message "NO" à toutes ses entrées
\* Chaque intermédiaire ayant reçu que des "YES" envoie un message "YES" à la node entrante lui ayant envoyé la plus petite valeur et un message "NO" aux autres
\* Chaque intermédiaire inverse les arêtes qui ont transporté un message "NO"
\* Chaque intermédiaire nettoie ses messages quand il à fini
DashYoIntermediary(n) == 
    /\ nodeState[n] = "Intermediary"
    /\ phase[n] = "-Yo"
    /\ \A m \in nodesLeaving[n] : \E msg \in msgs[n] : msg.node = m /\ msg.phase = "-Yo"
    /\  LET msgsDashYoPhase == {msg \in msgs[n] : msg.phase = "-Yo"}
        IN (\/  /\ \E m \in nodesLeaving[n] : \E msg \in msgsDashYoPhase : msg.node = m /\ msg.type = "NO"
                /\ LET noNodes == {m \in nodesLeaving[n] : \E msg \in msgs[n] : msg.node = m /\ msg.type = "NO"}
                    IN (/\ nodesEntering' = [nodesEntering EXCEPT ![n] = nodesLeaving[n] \intersect noNodes]
                        /\ nodesLeaving' = [nodesLeaving EXCEPT ![n] = nodesEntering[n] \cup (nodesLeaving[n] \ noNodes)]
                        /\ msgs' = [m \in Nodes |-> 
                            IF m \in nodesEntering[n] THEN msgs[m] \cup {[node |-> n, type |-> "NO", phase |-> "-Yo"]} 
                            ELSE IF m = n THEN {} ELSE msgs[m]])
            \/  /\ \A m \in nodesLeaving[n] : \E msg \in msgsDashYoPhase : msg.node = m /\ msg.type = "YES"
                /\ LET minVal == Min({msg.val : msg \in (msgs[n] \ msgsDashYoPhase)})
                    IN (LET notMinNodes == {m \in nodesEntering[n] : \E msg \in msgs[n] : msg.node = m /\ msg.val # minVal} 
                        IN (/\ nodesEntering' = [nodesEntering EXCEPT ![n] = nodesEntering[n] \ notMinNodes]
                            /\ nodesLeaving' = [nodesLeaving EXCEPT ![n] = nodesLeaving[n] \cup (nodesEntering[n] \intersect notMinNodes)]
                            /\ msgs' = [m \in Nodes |-> 
                                IF m \in notMinNodes THEN msgs[m] \cup {[node |-> n, type |-> "NO", phase |-> "-Yo"]} 
                                ELSE IF m \in nodesEntering[n] THEN msgs[m] \cup {[node |-> n, type |-> "YES", phase |-> "-Yo"]} 
                                    ELSE IF m = n THEN {} 
                                        ELSE msgs[m]])))
    /\ phase' = [phase EXCEPT ![n] = "Yo"]
    /\ UNCHANGED nodeState
    

\* Envoi des messages "YES" et "NO" d'une source
\* La source n'effectue la phase que si elle à reçu un message de toutes ses sorties
\* Les sources changent de sens les arêtes qui ont transporté un message "NO"
\* Les sources décident également si elles deviennent des sinks ou des intermédiaires ou restent des sources
\* Les sources nettoient leurs messages également
DashYoSource(n) == 
    /\ nodeState[n] = "Source"
    /\ phase[n] = "-Yo"
    /\ \A m \in nodesLeaving[n] : \E msg \in msgs[n] : msg.node = m /\ msg.phase = "-Yo"
    /\  LET msgsDashYoPhase == {msg \in msgs[n] : msg.phase = "-Yo"}
        IN (LET noNodes == {m \in nodesLeaving[n] : \E msg \in msgsDashYoPhase : msg.node = m /\ msg.type = "NO"}
            IN (/\ nodesEntering' = [nodesEntering EXCEPT ![n] = nodesLeaving[n] \intersect noNodes]
                /\ nodesLeaving' = [nodesLeaving EXCEPT ![n] = nodesLeaving[n] \ noNodes]
                /\ nodeState' = IF noNodes = {} 
                                THEN nodeState 
                                ELSE IF nodesLeaving'[n] = {} 
                                    THEN [nodeState EXCEPT ![n] = "Sink"] 
                                    ELSE [nodeState EXCEPT ![n] = "Intermediary"]
                /\ msgs' = [msgs EXCEPT ![n] = {}]))
    /\ phase' = [phase EXCEPT ![n] = "Yo"]


\* Etape "-Yo" comme décrit dans la page wikipedia
DashYoPhase(n) == 
    \/ DashYoSink(n)
    \/ DashYoIntermediary(n)
    \/ DashYoSource(n)

-------------------------------------------------------------

\* Définition du prochain état
YYNext == \E n \in Nodes : YoPhase(n) \/ DashYoPhase(n)

=============================================================