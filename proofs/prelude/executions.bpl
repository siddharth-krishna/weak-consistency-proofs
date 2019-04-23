// ----------------------------------------
// Definitions related to abstract executions:
// methods, invocations, linearization, visibility, etc
// 
// ----------------------------------------


type Method;

type Invoc;

// Boilerplate stuff for linear variables
function {:builtin "MapConst"} MapConstInvocBool(bool) : [Invoc]bool;
function {:inline} {:linear "this"} TidCollector(x: Invoc) : [Invoc]bool
{
  MapConstInvocBool(false)[x := true]
}


// ---------- Representation of execution and linearization

// hb(x, y) : x happens-before y.  // TODO make var, have actions to add these
// We assume there exists such a function, given by the client program
function hb(x: Invoc, y: Invoc) : bool;
axiom (forall n: Invoc :: !hb(n, n));

// A shared global variable that builds the linearization
var {:layer 1,2} lin: SeqInvoc;

// A map from invocations to the set of prior invocations visible to them
var {:layer 1,2} vis: [Invoc]SetInvoc;

// The map from invocations to method and argument values is encoded in the Invoc type
// so as to not further complicate the Queue ADT axioms above
// The map from invocations to return values is implicitly stored in the ghost vars
// retK & retS. Since return values are determined at the LPs, we store them at LP time.

procedure {:layer 1} intro_readLin() returns (s: SetInvoc)
  ensures {:layer 1} s == Set_ofSeq(lin);
{
  s := Set_ofSeq(lin);
}

procedure {:layer 1} intro_writeVis(n: Invoc, s: SetInvoc)
  modifies vis;
  ensures {:layer 1} vis == old(vis)[n := s];
{
  vis[n] := s;
}

procedure {:layer 1} {:inline 1} intro_writeLin(n: Invoc)
  requires {:layer 1} !Seq_elem(n, lin);
  // To show that linearization is consistent with happens-before
  requires {:layer 1} (forall n1 : Invoc :: hb(n1, n) ==> Seq_elem(n1, lin));
  ensures {:layer 1} Seq_elem(n, lin);
  modifies lin;
{
  lin := Seq_append(lin, n);
}

