// ----------------------------------------
// A simple queue implementation
// based on the Michael-Scott queue.
// Assumes an infinite array as the memory model.
//
// Use options -noinfer -typeEncoding:m -useArrayTheory
// ----------------------------------------


// ---------- Shared state and invariant

var {:layer 0, 1} queue: [int]int;

var {:layer 0, 1} head: int;
var {:layer 0, 1} tail: int;

const null: int;

function {:inline} Inv(queue: [int]int, head: int, tail: int) : (bool)
{
  0 <= head && 0 <= tail && head <= tail
  && (forall k: int :: head <= k && k <= tail ==> queue[k] != null)
}


// ---------- Primitives for manipulating ghost state

// Write to the queue
procedure {:atomic} {:layer 1} writeArray_spec(k, v: int)
  modifies queue;
{
  queue[k] := v;
}
procedure {:yields} {:layer 0} {:refines "writeArray_spec"}
  writeArray(k, v: int);

procedure {:atomic} {:layer 1} casArray_spec(k, ole, new: int) returns (b: bool)
  modifies queue;
{
  if (queue[k] == ole) {
    queue[k] := new;
    b := true;
  } else {
    b := false;
  }
}
procedure {:yields} {:layer 0} {:refines "casArray_spec"}
  casArray(k, ole, new: int) returns (b: bool);

// Read from the queue
procedure {:atomic} {:layer 1} readArray_spec(k: int)
  returns (v: int)
{
  v := queue[k];
}
procedure {:yields} {:layer 0} {:refines "readArray_spec"} readArray(k: int)
  returns (v: int);

procedure {:atomic} {:layer 1} readHead_spec() returns (v:int)
{ v := head; }

procedure {:yields} {:layer 0} {:refines "readHead_spec"} readHead() returns (v:int);

procedure {:atomic} {:layer 1} readTail_spec() returns (v:int)
{ v := tail; }

procedure {:yields} {:layer 0} {:refines "readTail_spec"} readTail() returns (v:int);

procedure {:atomic} {:layer 1} casHead_spec(ole, new: int) returns (b: bool)
  modifies head;
{
  if (head == ole) {
    head := new;
    b := true;
  } else {
    b := false;
  }
}
procedure {:yields} {:layer 0} {:refines "casHead_spec"}
  casHead(ole, new: int) returns (b: bool);


// ---------- queue methods:

procedure {:atomic} {:layer 2} atomic_pop() returns (t: int)
  modifies head, queue;
{
  assume true;
}

procedure {:yields} {:layer 1} {:refines "atomic_pop"} pop() returns (h: int)
requires {:layer 1} Inv(queue, head, tail);
ensures {:layer 1} Inv(queue, head, tail);
{
  var g: bool;
  var t, x: int;

  yield;
  assert {:layer 1} Inv(queue, head, tail);
  while (true)
    invariant {:layer 1} Inv(queue, head, tail);
  {
    call h := readHead();
    yield;
    assert {:layer 1} Inv(queue, head, tail);
    assert {:layer 1} h <= head;

    call t := readTail();
    yield;
    assert {:layer 1} Inv(queue, head, tail);
    assert {:layer 1} h <= head;
    assert {:layer 1} (h == head && h != t ==> head != tail);

    if (h != t) {
      call x := readArray(h);
      yield;
      assert {:layer 1} Inv(queue, head, tail);
      assert {:layer 1} h <= head;
      assert {:layer 1} (h == head && h != t ==> x == queue[head]);
      assert {:layer 1} (h == head && h != t ==> head != tail);

      call g := casHead(h, h + 1);
      if (g) {
        break;
      }
    }
    yield;
    assert {:layer 1} Inv(queue, head, tail);
  }
  yield;
  assert {:expand} {:layer 1} Inv(queue, head, tail);
}


procedure {:atomic} {:layer 2} atomic_push(x: int)
 modifies queue, tail;
{
  assume true;
}

procedure {:yields} {:layer 1} {:refines "atomic_push"} push(x: int)
  requires {:layer 1} Inv(queue, head, tail);
  ensures {:layer 1} Inv(queue, head, tail);
{
  var t, tn: int;
  var g: bool;

  yield;
  assert {:layer 1} Inv(queue, head, tail);
  while (true)
    invariant {:layer 1} Inv(queue, head, tail);
  {
    call t := readTail();
    yield;
    assert {:layer 1} Inv(queue, head, tail);
    // assert {:layer 1} next(queue)[t] == null ==> t == tail;

    call tn := readArray(t + 1);

    yield;
    assert {:layer 1} Inv(queue, head, tail);

    if (tn == null) {
      call g := casArray(t + 1, null, x);
      if (g) {
        break;
      }
    } // TODO else cas tail
    yield;
    assert {:layer 1} Inv(queue, head, tail);
  }
  yield;
  assert {:expand} {:layer 1} Inv(queue, head, tail);
}
  
/*
procedure {:atomic} {:layer 2} atomic_size() returns (x: int)
{}

procedure {:yields} {:layer 1} {:refines "atomic_size"} size() returns (x: int)
requires {:layer 1} Inv(queue, head, tail);
ensures {:layer 1} Inv(queue, head, tail);
{
  var c: int;

  yield;
  assert {:layer 1} Inv(queue, head, tail);

  x := 0;
  call c := readHead();

  yield;
  assert {:layer 1} Inv(queue, head, tail);
  assert {:layer 1} (Used[c] && Btwn(next(queue), c, c, head))
    || Btwn(next(queue), head, c, null);

  while (c != null)
    invariant {:layer 1} Inv(queue, head, tail);
    invariant {:layer 1} (Used[c] && Btwn(next(queue), c, c, head))
      || Btwn(next(queue), head, c, null);
  {
    x := x + 1;
    call c := Load(c); // TODO: load doesn't return next if not in dom!?
    yield;
    assert {:layer 1} Inv(queue, head, tail);
    assert {:layer 1} (Used[c] && Btwn(next(queue), c, c, head))
                        || Btwn(next(queue), head, c, null); // AtomicTransferToqueue breaks this, but it shouldn't!?
  }
  yield;
  assert {:layer 1} Inv(queue, head, tail);
  return;
}
*/
