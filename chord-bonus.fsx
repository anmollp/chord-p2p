#time "on"
#r "nuget: Akka.FSharp"

open System
open Akka.FSharp
open Akka.Actor
open System.Collections.Generic

let config = @"
akka {
  log-dead-letters = 10
  log-dead-letters-during-shutdown = on
}"

type MessageTypes = 
    | Supervise
    | Predecessor of int
    | FixFingers
    | CheckPredecessor
    | FindKey of int * int
    | FindKeyInSuccessor of int
    | Found of int * int * int
    | FindOperation of int
    | IdentifySuccesor
    | GivePredecessor
    | StabilizeNodes
    | Stabilize
    | StabilizeReq
    | StabilizeAck of int
    | Notify of int
    | Kill of int
    | LeaveChord of int

let randomNum (length) = Random().Next(0, length)

let ranStr n : string = 
    let r = Random()
    String(Array.init n (fun _ -> char (r.Next(97,123))))

let getNearestPowerOfTwo(number: int) = 
    int(Math.Pow(2.0, Math.Ceiling(Math.Log2(float(number)))))

let mutable currentNumNodes = 0

let mutable totalHops = 0

let maxBits(nodes) = int(Math.Log2(float(getNearestPowerOfTwo(nodes))))

let getHashForNodeOrKey(key: string) =  
    let n = System.Security.Cryptography.SHA1.Create()
    let x = BitConverter.ToString(n.ComputeHash(System.Text.Encoding.ASCII.GetBytes(key))).Replace("-", "")
    Convert.ToInt32(x.Substring(0,7), 16) % getNearestPowerOfTwo(currentNumNodes)

let system = ActorSystem.Create("Chord-System")

let mutable nodes = Set.empty

let removeKeys(dict: Dictionary<int, int>) = 
    dict |> Seq.filter( fun ele -> ele.Key > maxBits(currentNumNodes)) |> Seq.map(fun ele -> ele.Key)

let chordNodes = Dictionary<int, IActorRef>()

let calculate(n: int, k: int, bits: int) = (n + int(Math.Pow(2.0, float(k-1)))) % int(Math.Pow(2.0, float(bits)))
    
let rec getIthNeighbor(n: int, k: int, maxBits: int) = 
    let requiredNode = calculate(n,k,maxBits)
    let task = system.ActorSelection("akka://Chord-System/user/node-" + string(requiredNode)).ResolveOne(TimeSpan.FromMilliseconds(100.0))
    if task.IsFaulted then
        getIthNeighbor(requiredNode, 1, maxBits)
    else
        requiredNode

let sendMessage(n: int, id: int, hop: int, mailbox: IActorRef) = 
    let task = system.ActorSelection("akka://Chord-System/user/node-" + string(n)).ResolveOne(TimeSpan.FromMilliseconds(100.0)) 
    if task.IsFaulted then
        let ithNeighbor = getIthNeighbor(n, 1, maxBits(currentNumNodes))
        system.ActorSelection("akka://Chord-System/user/node-" + string(ithNeighbor)).Tell(FindKey(id, hop), mailbox)
    else
        system.ActorSelection("akka://Chord-System/user/node-" + string(n)).Tell(FindKey(id, hop), mailbox)

let sendFoundMessage(n, id, hop, mailbox) = 
    let task = system.ActorSelection("akka://Chord-System/user/node-" + string(n)).ResolveOne(TimeSpan.FromMilliseconds(100.0)) 
    if task.IsFaulted then
        let ithNeighbor = getIthNeighbor(n, 1, maxBits(currentNumNodes))
        system.ActorSelection("akka://Chord-System/user/node-" + string(ithNeighbor)).Tell(Found(id, ithNeighbor, hop), mailbox)
    else
        system.ActorSelection("akka://Chord-System/user/node-" + string(n)).Tell(Found(id, n, hop), mailbox)

let closestPrecedingNode(key: int, id: int, finger: Dictionary<int, int>, maxBits: int) = 
    let mutable iter = maxBits
    let mutable isFound = false
    let mutable node = key
    while iter > 0 && not isFound do
        if key > id then
            if (key < finger.Item(iter) && finger.Item(iter) <= getNearestPowerOfTwo(currentNumNodes)-1) then
                node <- getNearestPowerOfTwo(currentNumNodes)-1
                isFound <- true
            else
                if finger.Item(iter) < id then
                    node <- finger.Item(iter)
                    isFound <- true
                else 
                    iter <- iter - 1
        else if key < id then
            if key < finger.Item(iter) && finger.Item(iter) < id then
                node <- finger.Item(iter)
                isFound <- true
            else
                iter <- iter-1
        else
            node <- finger.Item(iter)
            isFound <- true
    node

let findSuccessor (key: int, id: int, successor: int, hop: int, mailbox: IActorRef, finger: Dictionary<int, int>, bits: int) =
    if key > successor then
        if (key < id && id <= getNearestPowerOfTwo(currentNumNodes)-1) then
            let n = getNearestPowerOfTwo(currentNumNodes)-1
            sendFoundMessage(n, id, hop+1, mailbox)
        else if 0 <= id  && id <= successor then
            if id = 0 then
                sendFoundMessage(0, id, hop+1, mailbox)
            else if id = successor then
                sendFoundMessage(0, id, hop+1, mailbox)
            else
                sendMessage(successor, id, hop, mailbox)
        else
            let nDash = closestPrecedingNode(key, id, finger, bits)
            sendMessage(nDash, id, hop, mailbox)
    else
        if key < id && id <= successor then
            sendFoundMessage(successor, id, hop+1, mailbox)
        else if key = id then
            sendFoundMessage(key, id, hop+1, mailbox)
        else
            let nDash = closestPrecedingNode(key, id, finger, bits)
            sendMessage(nDash, id, hop, mailbox)
       
let Node(key: int)(mailbox: Actor<_>) =
    let mutable finger = new Dictionary<int, int>()
    let mutable successor = -1
    let mutable predecessor = -1
    let mutable psuedoSuccesor = successor
    let mutable psuedokey = key
    let mutable next = 1
    let rec loop () = 
        actor {
            let! msg = mailbox.Receive()
            let sender = mailbox.Sender()
            match msg with 
            | FixFingers ->
                next <- next + 1
                if next > maxBits(nodes.Count) then
                    next <- 1
                removeKeys(finger) |> Seq.iter(fun k -> finger.Remove(k) |> ignore<bool>)
                finger.[next] <- getIthNeighbor(key, next, maxBits(currentNumNodes))
            | IdentifySuccesor -> 
                let ithNeighbor = getIthNeighbor(key, 1, maxBits(currentNumNodes))
                successor <- ithNeighbor 
            | Predecessor(node) -> predecessor <- node
            | GivePredecessor -> sender <! StabilizeAck(predecessor)
            | Stabilize -> 
                mailbox.Self <! StabilizeReq
            | StabilizeReq ->
                let task = system.ActorSelection("akka://Chord-System/user/node-" + string(successor)).ResolveOne(TimeSpan.FromMilliseconds(100.0))
                if task.IsFaulted then
                    mailbox.Self <! IdentifySuccesor
                system.ActorSelection("akka://Chord-System/user/node-" + string(successor)).Tell(GivePredecessor, mailbox.Self)
            | StabilizeAck(prdc) ->
                if successor = 0 then
                    psuedoSuccesor <- getNearestPowerOfTwo(currentNumNodes-1)
                if key < prdc && prdc < psuedoSuccesor then
                    successor <- prdc
                system.ActorSelection("akka://Chord-System/user/node-" + string(successor)).Tell(Notify(key), mailbox.Self)
            | Notify(prdc) -> 
                if key = 0 then
                   psuedokey <- getNearestPowerOfTwo(currentNumNodes-1)
                if predecessor = -1 || (predecessor < prdc && prdc < psuedokey) then
                    predecessor <- prdc
            | CheckPredecessor ->
                if predecessor <> -1 then
                    let task = system.ActorSelection("akka://Chord-System/user/node-" + string(predecessor)).ResolveOne(TimeSpan.FromMilliseconds(100.0))
                    if task.IsFaulted then
                        predecessor <- -1       
            | FindKey(id, hop) -> 
                printfn "***************************Finding: Song %d Hop %d*********************************" id (hop+1)
                printfn "Chord Size: %d" nodes.Count
                findSuccessor(key, id, successor, hop+1, mailbox.Self, finger, maxBits(currentNumNodes))
            | Found(id, s, hop) -> 
                printfn "I have song %d, and my name is Server %d" id s
                printfn "Snapshot of chord when song %d found" id 
                nodes|> Seq.iter (printf "%d~")
                printfn ""
                totalHops <- totalHops + hop
                printfn "***************************Found*********************************"
                let nodeId = int(mailbox.Self.Path.Name.Split("-").[1])
                if nodeId % 2 = 0 then
                    mailbox.Self.Tell(LeaveChord(nodeId), mailbox.Self)
            | LeaveChord(nodeId) -> 
                mailbox.Self.Tell(PoisonPill.Instance, mailbox.Self)
                nodes <- nodes.Remove(nodeId)
            | _ -> printfn "Invalid response(Node)"

            return! loop()
        }
    loop()

let Supervisor(mailbox: Actor<_>) =
    let timer = new Timers.Timer(float 100)
    let rec loop () = 
        actor {
            let! msg = mailbox.Receive()
            match msg with 
            | FindOperation(fileId) ->
                system.ActorSelection("akka://Chord-System/user/node-" + string(nodes.MinimumElement)).Tell(FindKey(fileId, 0), mailbox.Self)
            | Supervise ->
                timer.AutoReset <- true
                let eventHandler1 _ = mailbox.Self <! StabilizeNodes
                timer.Elapsed.Add eventHandler1
                timer.Start()
            | StabilizeNodes ->
                system.ActorSelection("akka://Chord-System/user/node-*").Tell(Stabilize, mailbox.Self)
                system.ActorSelection("akka://Chord-System/user/node-*").Tell(FixFingers, mailbox.Self)
                system.ActorSelection("akka://Chord-System/user/node-*").Tell(CheckPredecessor, mailbox.Self)
            | Kill(nodeId) -> 
                let task = system.ActorSelection("akka://Chord-System/user/node-" + string(nodeId)).ResolveOne(TimeSpan.FromSeconds(1.0)) 
                if task.IsFaulted then
                    let ithNeighbor = getIthNeighbor(nodeId, 1, maxBits(currentNumNodes))
                    system.ActorSelection("akka://Chord-System/user/node-" + string(ithNeighbor)).Tell(LeaveChord(ithNeighbor), mailbox.Self)
                else
                    system.ActorSelection("akka://Chord-System/user/node-" + string(nodeId)).Tell(LeaveChord(nodeId), mailbox.Self)            
            | _ -> printfn "Invalid response(Supervisor)"
            
            return! loop()
        }
    loop()

let joinChord key =
    if key <> 0 then
        let nodeName = "node-" + string(key)
        let node = spawn system nodeName (Node(key))
        chordNodes.Add(key, node)
        nodes <- nodes.Add(key)
        node <! IdentifySuccesor
        node <! FixFingers 

let buildChord numNodes =
    let mutable set = Set.empty
    let nodeName = "node-" + string(0)
    let node = spawn system nodeName (Node(0))
    chordNodes.Add(0, node)
    nodes <- nodes.Add(0)
    set <- set.Add(0)
    while set.Count <> numNodes do
        set <- set.Add(getHashForNodeOrKey(ranStr(100)))
    for key in set do
        joinChord key
    set

let main(numNodes: int, numRequests: int) =
    let supervisor = spawn system "Supervisor" (Supervisor)
    currentNumNodes <- numNodes
    let mutable remainingRequests = numRequests
    let x = buildChord(numNodes)
    printfn "Finished Building"
    Threading.Thread.Sleep(5000)
    supervisor <! Supervise
    while remainingRequests > 0 do
        Threading.Thread.Sleep(1000)
        let dataToFind =  ranStr(100)
        supervisor <! FindOperation(getHashForNodeOrKey dataToFind)
        remainingRequests <- remainingRequests-1
    printfn "Total hop length %d " totalHops
    printfn "~~~~~~~~~~~~~~~~~~~~~~~~Completed all requests~~~~~~~~~~~~~~~~~~~~~~~~~~~~~"
    system.WhenTerminated.Wait()

match fsi.CommandLineArgs with 
    | [|_; numNodes; numRequests|] -> main(int(numNodes), int(numRequests))
    | _ -> printfn "Error: Invalid Arguments."
    
