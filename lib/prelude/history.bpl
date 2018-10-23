// ---------- Representation of execution

// hb(x, y) : x happens-before y.
// We assume there exists such a function, given by the client program
function hb(x: Invoc, y: Invoc) : bool;
axiom (forall n: Invoc :: !hb(n, n));

/**
 * Interface members
 */

type History;
var {:layer 0,1} h: History;

function {:inline} History.called(h: History, i: Invoc): bool { _called(h)[i] }
function {:inline} History.returned(h: History, i: Invoc): bool { _returned(h)[i] }
function {:inline} History.pending(h: History, i: Invoc): bool { _called(h)[i] && !_returned(h)[i] }

procedure {:yields} {:layer 0} {:refines "_call"}
History.call(m: Method, args: ArgList) returns ({:linear "this"} this: Invoc);

procedure {:yields} {:layer 0} {:refines "_return"}
History.return({:linear "this"} this: Invoc);

/**
 * Internal members
 */

function _called(h: History): [Invoc] bool;
function _returned(h: History): [Invoc] bool;

procedure {:atomic} {:layer 1} _call(m: Method, args: ArgList)
  returns ({:linear "this"} this: Invoc)
  modifies h;
{
  var hh: History;
  assume m == Invoc.name(this);
  assume args == Invoc.args(this);
  assume (forall i: Invoc :: hb(i, this) ==> _returned(h)[i]);
  assume !_called(h)[this];
  assume !_returned(h)[this];
  assume _called(hh) == _called(h)[this := true];
  assume _returned(hh) == _returned(h);
  h := hh;
  assume _called(h)[this];
}

procedure {:atomic} {:layer 1} _return({:linear "this"} this: Invoc)
  modifies h;
{
  var hh: History;
  assume _called(hh) == _called(h);
  assume _returned(hh) == _returned(h)[this := true];
  h := hh;
  assume _returned(h)[this];
}
