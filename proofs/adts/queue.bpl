// ----------------------------------------
//
// The queue Abstract Data Type
// 
// ----------------------------------------


const unique Queue.push, Queue.pop, Queue.size: Method;

function invoc_m(n: Invoc) : Method;
function invoc_k(n: Invoc) : Key;

type Queue.State;

function Queue.stateArray(s: Queue.State) : [int]Key;
function Queue.stateHead(s: Queue.State) : int;
function Queue.stateTail(s: Queue.State) : int;

function Queue.ofSeq(s: SeqInvoc) : Queue.State;


// ---------- Axioms of the queue ADT

// Effect of pop to the abstract state of a Queue
axiom (forall s: SeqInvoc, n: Invoc :: {Queue.ofSeq(Seq_append(s, n))}
  invoc_m(n) == Queue.pop
  ==> ((Queue.stateHead(Queue.ofSeq(s)) != Queue.stateTail(Queue.ofSeq(s))
      && Queue.stateHead(Queue.ofSeq(Seq_append(s, n)))
      == Queue.stateHead(Queue.ofSeq(s)) + 1)
    || (Queue.stateHead(Queue.ofSeq(s)) == Queue.stateTail(Queue.ofSeq(s))
      && Queue.stateHead(Queue.ofSeq(Seq_append(s, n)))
      == Queue.stateHead(Queue.ofSeq(s))))
  && Queue.stateTail(Queue.ofSeq(Seq_append(s, n)))
    == Queue.stateTail(Queue.ofSeq(s))
  && Queue.stateArray(Queue.ofSeq(Seq_append(s, n)))
    == Queue.stateArray(Queue.ofSeq(s)));

// Effect of push to the abstract state of a Queue
axiom (forall s: SeqInvoc, n: Invoc :: {Queue.ofSeq(Seq_append(s, n))}
  invoc_m(n) == Queue.push
  ==> Queue.stateHead(Queue.ofSeq(Seq_append(s, n)))
    == Queue.stateHead(Queue.ofSeq(s))
  && Queue.stateTail(Queue.ofSeq(Seq_append(s, n)))
    == Queue.stateTail(Queue.ofSeq(s)) + 1
  && Queue.stateArray(Queue.ofSeq(Seq_append(s, n)))
    == Queue.stateArray(Queue.ofSeq(s))[
      Queue.stateTail(Queue.ofSeq(s)) := invoc_k(n)]);

// Effect of size to the abstract state of a Queue
axiom (forall s: SeqInvoc, n: Invoc :: {Queue.ofSeq(Seq_append(s, n))}
  invoc_m(n) == Queue.size
  ==> Queue.stateHead(Queue.ofSeq(Seq_append(s, n)))
    == Queue.stateHead(Queue.ofSeq(s))
  && Queue.stateTail(Queue.ofSeq(Seq_append(s, n)))
    == Queue.stateTail(Queue.ofSeq(s))
  && Queue.stateArray(Queue.ofSeq(Seq_append(s, n)))
    == Queue.stateArray(Queue.ofSeq(s)));


// ---------- Atomic specification program:

// procedure {:atomic} {:layer 2} hb_action(n1: Invoc, n2: Invoc)

procedure {:atomic} {:layer 2} push_call_atomic({:linear "this"} this: Invoc) {}

procedure {:atomic} {:layer 2} push_atomic(k: Key, x: Ref,
    {:linear_in "FP"} xFP: [Ref]bool, {:linear "this"} this: Invoc)
  modifies lin, vis;
{
  var my_vis: SetInvoc;

  // Satisfies its functional spec  // TODO instead, add to Inv that abs execution satisfies S
  assume true;

  assume Consistency.absolute(lin, vis, this, my_vis);

  lin := Seq_append(lin, this);
  vis[this] := my_vis;
}

procedure {:atomic} {:layer 2} push_return_atomic({:linear "this"} this: Invoc) {}

procedure {:atomic} {:layer 2} pop_call_atomic({:linear "this"} this: Invoc) {}

procedure {:atomic} {:layer 2} pop_atomic({:linear "this"} this: Invoc) returns (k: Key)
  modifies lin, vis;
{
  var my_vis: SetInvoc;

  // Satisfies its functional spec
  assume k == Queue.stateArray(Queue.ofSeq(lin))[Queue.stateHead(Queue.ofSeq(lin))];

  assume Consistency.absolute(lin, vis, this, my_vis);

  lin := Seq_append(lin, this);
  vis[this] := my_vis;
}

procedure {:atomic} {:layer 2} pop_return_atomic({:linear "this"} this: Invoc) {}

procedure {:atomic} {:layer 2} size_call_atomic({:linear "this"} this: Invoc) {}

procedure {:atomic} {:layer 2} size_atomic({:linear "this"} this: Invoc) returns (s: int)
  modifies lin, vis;
{
  var my_vis: SetInvoc;

  // Satisfies its functional spec
  assume s == Queue.stateTail(Queue.ofSeq(Seq_restr(lin, my_vis)))
    - Queue.stateHead(Queue.ofSeq(Seq_restr(lin, my_vis)));

  assume Consistency.monotonic(lin, vis, this, my_vis);

  lin := Seq_append(lin, this);
  vis[this] := my_vis;
}

procedure {:atomic} {:layer 2} size_return_atomic({:linear "this"} this: Invoc) {}

