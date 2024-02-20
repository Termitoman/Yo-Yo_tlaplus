\* Module qui abstrait l'algorithme d'élection de leader Yo-Yo avec élagage.
\* Ecrit par Ludovic Yvoz pour le cours de Vérification Algorithmique

------------------------ MODULE YoYoPruning ------------------------
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
\* pruned : Pour chaque node, si il a été élagué ou non
VARIABLE nodeState, nodesEntering, nodesLeaving, msgs, phase, pruned

\* Messages : L'ensemble des messages possibles entre nodes
Messages == [node : Nodes, val : Nodes, phase : {"Yo"}]  \cup  [node : Nodes, type : {"YES", "NO"}, phase : {"-Yo"}, pruned : BOOLEAN]

-------------------------------------------------------------

\* Vérifie que les variables restent dans un état correct
YYTypeOK == 
    /\ nodeState \in [Nodes -> {"Source", "Intermediary", "Sink", "Leader"}]
    /\ nodesEntering \in [Nodes -> SUBSET Nodes]
    /\ nodesLeaving \in [Nodes -> SUBSET Nodes]
    /\ msgs \in [Nodes -> SUBSET Messages]
    /\ phase \in [Nodes -> {"Yo", "-Yo"}]
    /\ pruned \in [Nodes -> BOOLEAN]

\* Définit l'ensemble des nodes voisins d'un node
Neighbors(n) == {m \in Nodes : {m,n} \in Edges}

\* Initialisation des variables et préprocessing
\* On effectue le préprocessing de façon synchrone car cette phase n'est pas très intéressante
YYInit == 
    /\ nodesEntering = [n \in Nodes |-> { m \in Neighbors(n) : m < n}]
    /\ nodesLeaving = [n \in Nodes |-> { m \in Neighbors(n) : m > n}]
    /\ nodeState = [n \in Nodes |-> 
                    IF nodesEntering[n] = {} /\ nodesLeaving[n] = {} /\ Cardinality(Nodes) = 1 THEN "Leader"
                    ELSE IF nodesLeaving[n] = Neighbors(n) THEN "Source"
                    ELSE IF nodesEntering[n] = Neighbors(n) THEN "Sink"
                    ELSE "Intermediary"]
    /\ msgs = [n \in Nodes |-> {}]
    /\ phase = [n \in Nodes |-> "Yo"]
    /\ pruned = [n \in Nodes |-> FALSE]

\* Définition d'invariants controlant l'état des variables

YYEnteringOK == \A n \in Nodes : nodesEntering[n] \subseteq Neighbors(n)

YYLeavingOK == \A n \in Nodes : nodesLeaving[n] \subseteq Neighbors(n)

YYStateOK == \A n \in Nodes : 
    /\ nodeState[n] = "Source" => nodesEntering[n] = {}
    /\ nodeState[n] = "Sink" => nodesLeaving[n] = {}
    /\ nodeState[n] = "Intermediary" => nodesEntering[n] # {} /\ nodesLeaving[n] # {}
    /\ nodeState[n] = "Leader" => nodesEntering[n] = {} /\ nodesLeaving[n] = {} /\ pruned[n] = FALSE

YYMsgsOK == \A n \in Nodes : 
    /\ \A msg \in msgs[n] : msg.node \in Neighbors(n)
    /\ \A m \in Neighbors(n) : Cardinality({msg \in msgs[n] : msg.node = m /\ msg.phase = "Yo"}) <= 1
    /\ \A m \in Neighbors(n) : Cardinality({msg \in msgs[n] : msg.node = m /\ msg.phase = "-Yo"}) <= 1

\* Définition d'un invariant faux quand l'algorithme termine pour regarder l'éxécution de l'algorithme
YYFalse == \A n \in Nodes : nodeState[n] # "Leader"

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
\* Cette phase ne s'éxécute que si la node à reçu un message de toutes ses entrées et que la phase est "Yo" et qu'elle n'est pas élaguée

YoPhaseIntermediarySink(n) == 
    /\ nodeState[n] \in {"Intermediary", "Sink"}
    /\ phase[n] = "Yo"
    /\ pruned[n] = FALSE
    /\ \A m \in nodesEntering[n] : \E msg \in msgs[n] : msg.node = m /\ msg.phase = "Yo"
    /\ LET msgsYoPhase == {msg \in msgs[n] : msg.phase = "Yo"}
        IN (LET min == Min({msg.val : msg \in msgsYoPhase})
            IN(msgs' = [m \in Nodes |-> 
                IF m \in nodesLeaving[n] 
                THEN msgs[m] \cup {[node |-> n, val |-> min, phase |-> "Yo"]} 
                ELSE msgs[m]]))
    /\ phase' = [phase EXCEPT ![n] = "-Yo"]

\* Etape "Yo" comme décrit dans la page wikipedia
\* Cette étape ne se fait que si toutes les nodes ont fini l'étape de pré-traitement
\* Chaque source envoie un message contenant son ID à chaque node sortant
\* Chaque intermédiaire envoie un message contenant l'ID de la source (minimum entre tous les entrants) à chaque node sortant
\* Les sink ne font rien pour cette phase
YoPhase(n) == 
    /\  \/ EnvoiIDSource(n)
        \/ YoPhaseIntermediarySink(n)
    /\ UNCHANGED <<nodeState, nodesEntering, nodesLeaving, pruned>>

-------------------------------------------------------------

\* opérateur qui retourne l'état d'un noeud selon ses entrée, ses sorties, si il est élagué et son état précédent
ComputeState(nEnter, nLeave, prnd, previous) == 
    IF prnd THEN previous
    ELSE IF nEnter = {} /\ nLeave = {} THEN "Leader"
    ELSE IF nEnter = {} THEN "Source"
    ELSE IF nLeave = {} THEN "Sink"
    ELSE "Intermediary"

\* Opérateur qui indique si la node est la node choisie parmi les nodes ayant envoyé un message avec la même valeur que le message que cette node à envoyé
IsntChosenNode(m, n) ==
    LET msgsYoPhase == {msg \in msgs[n] : msg.phase = "Yo"}
    IN  (LET msg_m == CHOOSE msg \in msgsYoPhase : msg.node = m
        IN  LET winner == CHOOSE msg \in msgsYoPhase : msg.val = msg_m.val
            IN  m # winner.node) 

\* Envoi des messages de sink
\* Le sink n'effectue la phase que si il à reçu un message de toutes ses entrées et qu'il n'est pas élagué
\* Chaque sink envoie un message "YES" à la node entrante lui ayant envoyé un message avec la plus petite valeur et un message "NO" aux autres
\* Chaque sink inverse les arêtes qui ont transporté un message "NO"
\* Chaque sink nettoie ses messages quand il à fini
\* Un sink devient élagué si il n'a qu'une seule entrée
\* Un sink qui à reçu plusieurs messages avec la même valeur les élagues toutes sauf une (choisie arbitrairement)
DashYoSink(n) == 
    /\ nodeState[n] = "Sink"
    /\ phase[n] = "-Yo"
    /\ pruned[n] = FALSE
    /\ \A m \in nodesEntering[n] : \E msg \in msgs[n] : msg.node = m /\ msg.phase = "Yo"
    /\  IF Cardinality(nodesEntering[n]) = 1 
        THEN (
            /\ pruned' = [pruned EXCEPT ![n] = TRUE] 
            /\ msgs' = [m \in Nodes |-> 
                IF m \in nodesEntering[n] 
                THEN msgs[m] \cup {[node |-> n, type |-> "YES", phase |-> "-Yo", pruned |-> TRUE]} 
                ELSE IF m = n 
                THEN {} 
                ELSE msgs[m]]
            /\ nodesEntering' = [nodesEntering EXCEPT ![n] = {}]
            /\ UNCHANGED <<nodesLeaving, phase>>)
        ELSE (  LET msgsYoPhase == {msg \in msgs[n] : msg.phase = "Yo"}
                    valsRcvd == {msg.val : msg \in msgsYoPhase} 
                    minVal == Min(valsRcvd)
                    senders(v) == {m \in nodesEntering[n] :
                        [phase |-> "Yo", node |-> m, val |-> v] \in msgs[n]}
                    value(m) == (CHOOSE msg \in msgsYoPhase : msg.node = m).val
                IN  (\E keep \in {f \in [valsRcvd -> nodesEntering[n]] :
                    \A v \in valsRcvd : f[v] \in senders(v)} :
                        /\ msgs' = [m \in Nodes |->
                            IF m \in senders(minVal)
                            THEN msgs[m] \cup {[phase |-> "-Yo", node |-> n, type |-> "YES", pruned |-> m # keep[minVal]]}
                            ELSE IF m \in nodesEntering[n]
                            THEN msgs[m] \cup {[phase |-> "-Yo", node |-> n, type |-> "NO", pruned |-> m # keep[value(m)]]}
                            ELSE IF m = n THEN {}
                            ELSE msgs[m]]
                        /\ nodesEntering' = [nodesEntering EXCEPT ![n] = {keep[minVal]}]
                        /\ nodesLeaving' = [nodesLeaving EXCEPT ![n] = {keep[v] : v \in (valsRcvd \ {minVal})}]))
    /\ phase' = [phase EXCEPT ![n] = "Yo"]
    /\ UNCHANGED pruned

\* Envoi des messages d'intermédiaire
\* L'intérmédiaire n'effectue la phase que si il à reçu un message de toutes ses sorties et qu'il n'est pas élagué (pas sensé arriver)
\* Chaque intermédiaire ayant reçu un "NO" envoie un message "NO" à toutes ses entrées
\* Chaque intermédiaire ayant reçu que des "YES" envoie un message "YES" à la node entrante lui ayant envoyé la plus petite valeur et un message "NO" aux autres
\* Chaque intermédiaire inverse les arêtes qui ont transporté un message "NO"
\* Chaque intermédiaire nettoie ses messages quand il à fini
\* Un interméiaire qui reçoit un message contenant un indicateur que l'envoyeur est élagué coupe le lien avec cet envoyeur
\* Un intermédiaire qui à reçu la même valeur de plusieurs de ses entrées les élagues toutes sauf une (choisie arbitrairement)
DashYoIntermediary(n) == 
    /\ nodeState[n] = "Intermediary"
    /\ phase[n] = "-Yo"
    /\ \A m \in nodesLeaving[n] : \E msg \in msgs[n] : msg.node = m /\ msg.phase = "-Yo"
    /\  LET msgsDashYoPhase == {msg \in msgs[n] : msg.phase = "-Yo"}
        IN (LET prunedNodes == LET prunedMsg == {msg \in msgsDashYoPhase : msg.pruned = TRUE} IN ({msg.node : msg \in prunedMsg})
            IN (IF \E m \in nodesLeaving[n] : \E msg \in msgsDashYoPhase : msg.node = m /\ msg.type = "NO"
                THEN LET noNodes == {m \in nodesLeaving[n] \ prunedNodes : \E msg \in msgsDashYoPhase : msg.node = m /\ msg.type = "NO"}
                    IN (LET msgsYoPhase == {msg \in msgs[n] : msg.phase = "Yo"}
                            valsRcvd == {msg.val : msg \in msgsYoPhase} 
                            senders(v) == {m \in nodesEntering[n] :
                                [phase |-> "Yo", node |-> m, val |-> v] \in msgs[n]}
                            value(m) == (CHOOSE msg \in msgsYoPhase : msg.node = m).val 
                        IN  (\E keep \in {f \in [valsRcvd -> nodesEntering[n]] :
                            \A v \in valsRcvd : f[v] \in senders(v)} :
                                /\ msgs' = [m \in Nodes |->
                                    IF m \in nodesEntering[n]
                                    THEN msgs[m] \cup {[phase |-> "-Yo", node |-> n, type |-> "NO", pruned |-> m # keep[value(m)]]}
                                    ELSE IF m = n 
                                    THEN {msg \in msgs[n] : msg.phase = "Yo" /\ \E msg2 \in msgsDashYoPhase : msg2.node = msg.node}
                                    ELSE msgs[m]]
                                /\ nodesEntering' = [nodesEntering EXCEPT ![n] = nodesLeaving[n] \intersect noNodes]
                                /\ nodesLeaving' = [nodesLeaving EXCEPT ![n] = ((nodesLeaving[n] \ prunedNodes) \ noNodes) \cup {keep[v] : v \in (valsRcvd)}]))
                ELSE LET msgsYoPhase == {msg \in msgs[n] : msg.phase = "Yo"}
                        valsRcvd == {msg.val : msg \in msgsYoPhase} 
                        minVal == Min(valsRcvd)
                        senders(v) == {m \in nodesEntering[n] :
                            [phase |-> "Yo", node |-> m, val |-> v] \in msgs[n]}
                        value(m) == (CHOOSE msg \in msgsYoPhase : msg.node = m).val
                    IN  (\E keep \in {f \in [valsRcvd -> nodesEntering[n]] :
                        \A v \in valsRcvd : f[v] \in senders(v)} :
                            /\ msgs' = [m \in Nodes |->
                                IF m \in senders(minVal)
                                THEN msgs[m] \cup {[phase |-> "-Yo", node |-> n, type |-> "YES", pruned |-> m # keep[minVal]]}
                                ELSE IF m \in nodesEntering[n]
                                THEN msgs[m] \cup {[phase |-> "-Yo", node |-> n, type |-> "NO", pruned |-> m # keep[value(m)]]}
                                ELSE IF m = n 
                                THEN {msg \in msgs[n] : msg.phase = "Yo" /\ \E msg2 \in msgsDashYoPhase : msg2.node = msg.node}
                                ELSE msgs[m]]
                            /\ nodesEntering' = [nodesEntering EXCEPT ![n] = {keep[minVal]}]
                            /\ nodesLeaving' = [nodesLeaving EXCEPT ![n] = (nodesLeaving[n] \ prunedNodes) \cup {keep[v] : v \in (valsRcvd \ {minVal})}])))
    /\ phase' = [phase EXCEPT ![n] = "Yo"]
    /\ UNCHANGED pruned

\* Envoi des messages "YES" et "NO" d'une source
\* La source n'effectue la phase que si elle à reçu un message de toutes ses sorties et qu'elle n'est pas élaguée (pas sensé arriver)
\* Les sources changent de sens les arêtes qui ont transporté un message "NO"
\* Les sources décident également si elles deviennent des sinks ou des intermédiaires ou restent des sources
\* Les sources nettoient leurs messages également
\* Si une source reçoit un message contenant un indicateur que l'envoyeur est élagué, elle coupe le lien avec cet envoyeur
DashYoSource(n) == 
    /\ nodeState[n] = "Source"
    /\ phase[n] = "-Yo"
    /\ pruned[n] = FALSE
    /\ \A m \in nodesLeaving[n] : \E msg \in msgs[n] : msg.node = m /\ msg.phase = "-Yo"
    /\  LET msgsDashYoPhase == {msg \in msgs[n] : msg.phase = "-Yo"}
        IN (LET prunedNodes == LET prunedMsg == {msg \in msgsDashYoPhase : msg.pruned = TRUE} IN ({msg.node : msg \in prunedMsg})
            IN  LET noNodes == {m \in nodesLeaving[n] \ prunedNodes : \E msg \in msgsDashYoPhase : msg.node = m /\ msg.type = "NO"}
                IN (/\ nodesEntering' = [nodesEntering EXCEPT ![n] = noNodes]
                    /\ nodesLeaving' = [nodesLeaving EXCEPT ![n] = (nodesLeaving[n] \ prunedNodes) \ noNodes]
                    /\ msgs' = [msgs EXCEPT ![n] = {msg \in msgs[n] : msg.phase = "Yo" /\ \E msg2 \in msgsDashYoPhase : msg2.node = msg.node}]))
    /\ phase' = [phase EXCEPT ![n] = "Yo"]
    /\ UNCHANGED pruned


\* Etape "-Yo" comme décrit dans la page wikipedia
DashYoPhase(n) == 
    /\  \/ DashYoSink(n)
        \/ DashYoIntermediary(n)
        \/ DashYoSource(n)
    /\ nodeState' = [nodeState EXCEPT ![n] = ComputeState(nodesEntering'[n], nodesLeaving'[n], pruned'[n], nodeState[n])]

-------------------------------------------------------------

\* Définition du prochain état
YYNext == \E n \in Nodes : YoPhase(n) \/ DashYoPhase(n)

=============================================================