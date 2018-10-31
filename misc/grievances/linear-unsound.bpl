type Loc;
const null: Loc;

type Heap;
function {:linear "Node"} dom(Heap): [Loc]bool;
function next(Heap): [Loc]Loc;
function data(Heap): [Loc]int;
function {:builtin "MapConst"} MapConstLocBool(bool) : [Loc]bool;

function EmptyLmap(): (Heap);
axiom (dom(EmptyLmap()) == MapConstLocBool(false));

function Add(h: Heap, l: Loc, v: Loc): (Heap);
axiom (forall h: Heap, l: Loc, v: Loc :: dom(Add(h, l, v)) == dom(h)[l:=true] && next(Add(h, l, v)) == next(h)[l := v]);


var {:linear "Node"} {:layer 0,1} heap: Heap;


procedure {:atomic} {:layer 1} alloc_spec(x: Loc)
  modifies heap;
{
  assert !dom(heap)[x];
  heap := Add(heap, x, null);
}
procedure {:yields} {:layer 0} {:refines "alloc_spec"} alloc(x: Loc);


procedure {:atomic} {:layer 2} test_spec(x: Loc, {:linear_in "Node"} x_heap: Heap)
{ assume true; }

procedure {:yields} {:layer 1} {:refines "test_spec"} test(x: Loc, {:linear_in "Node"} x_heap: Heap)
  requires {:layer 1} dom(x_heap)[x];
{
  yield;
  call alloc(x);
  assert {:layer 1} false;
  yield;
}

