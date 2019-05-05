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

// hb[x][y] : x happens-before y.
var {:layer 1,2} hb: [Invoc][Invoc]bool;

// A shared global variable that builds the linearization
var {:layer 1,2} lin: SeqInvoc;

// A map from invocations to the set of prior invocations visible to them
var {:layer 1,2} vis: [Invoc]SetInvoc;

// The map from invocations to method and argument values is encoded in the Invoc
// type so as to not further complicate the ADT axioms.

// The map from invocations to return values
// Since return values are determined at the LPs, we store them at LP time.
type RetVal;
function RetVal_ofInt(int) : RetVal;
function RetVal_ofBool(bool) : RetVal;
var {:layer 1,2} ret: [Invoc]RetVal;

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
  requires {:layer 1} (forall n1 : Invoc :: hb[n1][n] ==> Seq_elem(n1, lin));
  ensures {:layer 1} Seq_elem(n, lin);
  modifies lin;
{
  lin := Seq_append(lin, n);
}

procedure {:layer 1} {:inline 1} intro_writeHb(n1: Invoc, n2: Invoc)
  modifies hb;
{
  hb[n1] := hb[n1][n2 := true];
}

procedure {:layer 1} {:inline 1} intro_writeRet(n: Invoc, v: RetVal)
  modifies ret;
{
  ret[n] := v;
}


// ---------- Consistency levels

function {:inline} Consistency.absolute(hb: [Invoc]SetInvoc, lin: SeqInvoc,
    vis: [Invoc]SetInvoc, n: Invoc, n_vis: SetInvoc): bool {
  n_vis == Set_ofSeq(lin)
}

function {:inline} Consistency.monotonic(hb: [Invoc]SetInvoc, lin: SeqInvoc,
    vis: [Invoc]SetInvoc, n: Invoc, n_vis: SetInvoc): bool {
  (forall i: Invoc :: hb[i][n] ==> Set_subset(vis[i], n_vis))
}
