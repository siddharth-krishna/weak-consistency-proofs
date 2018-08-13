// A simplified hash table implementation with weakly consistent contains method

type Invoc;

type SeqInvoc;  // sequence of invocations

// Create an invocation. Methods are: 0 - put, 1 - get, 2 - contains
function createInvoc(m: int, k: int, v: int) returns (i: Invoc);

function append(s: SeqInvoc, i: Invoc) returns (t: SeqInvoc);

// A function to calculate the abstract state after a sequential execution
function state(s: SeqInvoc) returns (m: [int]int);

// A function to restrict a SeqInvoc to invocations involving key k
function restr(s: SeqInvoc, k: int) returns (t: SeqInvoc);

// The mapping of key k depends only invocations involving k
axiom (forall s: SeqInvoc, k: int :: state(s)[k] == state(restr(s, k))[k]);


// ---------- Some lemmas that we need

procedure lemma_append_effect(s1, s2: SeqInvoc, o: Invoc, m, k, v: int)
  requires s2 == append(s1, o) && o == createInvoc(m, k, v);
  ensures (forall i: int :: i != k ==> state(s1)[i] == state(s2)[i]);
  ensures m == 0 ==> state(s2)[k] == v;
{
  assume false;
}


// ---------- Logical and concrete shared state

var lin: SeqInvoc;  // a shared global variable that builds the linearization
// Need to restrict actions/interference to only increase lin

// Concrete state of implementation
var table: [int]int;
var tableLen: int;


// ---------- Procedures/methods

procedure put(k: int, v: int)
  modifies table, lin;
  requires 0 <= k && k < tableLen;
  requires (forall i: int :: 0 <= i && i < tableLen ==> table[i] == state(lin)[i]);
  ensures (forall i: int :: 0 <= i && i < tableLen ==> table[i] == state(lin)[i]);
{
  var old_lin: SeqInvoc;
  var invoc: Invoc;

  table[k] := v;

  old_lin := lin;
  invoc := createInvoc(0, k, v);
  lin := append(lin, invoc);
  call lemma_append_effect(old_lin, lin, invoc, 0, k, v);
}

procedure get(k: int) returns (v: int)
  requires 0 <= k && k < tableLen;
  requires (forall i: int :: 0 <= i && i < tableLen ==> table[i] == state(lin)[i]);
  ensures (forall i: int :: 0 <= i && i < tableLen ==> table[i] == state(lin)[i]);
{
  v := table[k];

  assert state(lin)[k] == v;
  lin := append(lin, this);
  return v;
}
