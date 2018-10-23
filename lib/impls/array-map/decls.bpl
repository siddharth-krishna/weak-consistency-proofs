// ---------- Logical and concrete shared state

// Abstract state of ADT
var {:layer 1,2} abs: Map.State;

// Visibility per location of concrete state
var {:layer 1,1} tabvis: [int]Set;


// Concrete state of implementation
var {:layer 0,1} table: [int]int;
const tabLen: int;
axiom 0 < tabLen;


function {:inline} abstracts(conc: [int]int, abs: Map.State) : bool
{
  (forall i: int :: 0 <= i && i < tabLen ==> conc[i] == abs[i])
}

// The invariants
function {:inline} tableInv(table: [int]int, tabLen: int, tabvis: [int]Set,
                            abs: Map.State,
                            lin: Seq, vis: Vis,
                            h: History) : bool
{
  abstracts(table, abs)
  && Set.unionAll(tabvis, 0, tabLen) == Set.ofSeq(lin)
  && (forall i: int :: 0 <= i && i < tabLen ==> Map.ofVis(tabvis[i], lin)[i] == abs[i])
  && (forall i: int :: 0 <= i && i < tabLen ==>
      Map.ofVis(tabvis[i], lin)[i] == Map.ofVis(Map.restr(Set.ofSeq(lin), i), lin)[i])
  && (forall i: int :: 0 <= i && i < tabLen ==> Set.subset(Map.restr(Set.ofSeq(lin), i), tabvis[i]))
  && (forall i: int :: 0 <= i && i < tabLen ==> Set.subset(tabvis[i], Set.ofSeq(lin)))
  && (forall i: int, n: Invoc :: 0 <= i && i < tabLen && Set.elem(n, tabvis[i])
      ==> Map.key(n) == i)
  // Used to infer that invocations don't modify vis after they've returned
  && (forall n1, n2 : Invoc :: History.called(h,n1) && hb(n2, n1) ==> History.returned(h,n2))
  // Sanity conditions on vis sets
  && (forall n1, n2 : Invoc :: Set.elem(n2, vis[n1]) ==> Set.elem(n2, tabvis[Map.key(n2)]))
  && (forall n1, n2 : Invoc :: Set.elem(n2, vis[n1]) ==> 0 <= Map.key(n2) && Map.key(n2) < tabLen)
  // To establish precondition of intro_writeLin
  && (forall n: Invoc :: History.returned(h,n) ==> Seq.elem(n, lin))
}

// ---------- Primitives/helpers for modifying global state

// Write to the table
procedure {:atomic} {:layer 1} writeTable_spec(k, v: int)
  modifies table;
{
  table[k] := v;
}
procedure {:yields} {:layer 0} {:refines "writeTable_spec"}
  writeTable(k, v: int);

// Read from the table
procedure {:atomic} {:layer 1} readTable_spec(k: int)
  returns (v: int)
{
  v := table[k];
}
procedure {:yields} {:layer 0} {:refines "readTable_spec"} readTable(k: int)
  returns (v: int);


// ---------- Introduction actions:

procedure {:layer 1} intro_add_tabvis(k: int, {:linear "this"} n: Invoc)
  // TODO why don't these follow from the body?
  ensures {:layer 1} tabvis == old(tabvis)[k := Set.add(old(tabvis)[k], n)];
  modifies tabvis;
{
  tabvis[k] := Set.add(tabvis[k], n);
}

procedure {:layer 1} intro_read_tabvis_range(i, j: int) returns (s: Set);
  ensures {:layer 1} s == Set.unionAll(tabvis, i, j);
  ensures {:layer 1} (forall n: Invoc, k: int :: Set.elem(n, tabvis[k]) && i <= k && k < j ==> Set.elem(n, s));
  // TODO show these
  ensures {:layer 1} (forall n1: Invoc :: Set.elem(n1, s) ==> Set.elem(n1, tabvis[Map.key(n1)]));
  ensures {:layer 1} (forall n1: Invoc :: Set.elem(n1, s)
    ==> i <= Map.key(n1) && Map.key(n1) < j);

procedure {:layer 1} intro_read_tabvis(k: int) returns (s: Set)
  ensures {:layer 1} s == tabvis[k];
{
  s := tabvis[k];
}

procedure {:layer 1} {:inline 1} intro_writeAbs(k: int, v: int)
  modifies abs;
{
  // FIXME this breaks an abstraction boundary: the map ADT should dictate
  // itself how it is updated.
  abs[k] := v;
}
