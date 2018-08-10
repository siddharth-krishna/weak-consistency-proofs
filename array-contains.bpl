// A simplified hash table implementation with weakly consistent contains method

type Invoc;

type SeqInvoc;  // sequence of invocations

function createInvoc(m: int, k: int, v: int) returns (i: Invoc);

function append(s: SeqInvoc, i: Invoc) returns (t: SeqInvoc);

// A function to calculate the abstract state after a sequential execution
function state(s: SeqInvoc) returns (m: [int]int);

// A function to restrict a SeqInvoc to invocations involving key k
function restr(s: SeqInvoc, k: int) returns (t: SeqInvoc);

// The mapping of key k depends only invocations involving k
axiom (forall s: SeqInvoc, k: int :: state(s)[k] == state(restr(s, k))[k]);

var lin: SeqInvoc;  // a shared global variable that builds the linearization
// Need to restrict actions/interference to only increase lin


// Concrete state of implementation
var table: [int]int;
var tableLen: int;

procedure put(k: int, v: int)
  modifies table, lin;
  requires 0 <= k && k < tableLen;
  requires (forall i: int :: 0 <= i && i < tableLen ==> table[i] == state(lin)[i]);
  ensures (forall i: int :: 0 <= i && i < tableLen ==> table[i] == state(lin)[i]);
{
  table[k] := v;
  lin := append(lin, createInvoc(0, k, v));
}

