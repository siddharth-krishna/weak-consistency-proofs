/**
 * Imported declarations
 */

// type Invoc;
// type Method
// type ArgList
// function Invoc.name(i: Invoc): Method;
// function Invoc.args(i: Invoc): ArgList;
// function hb(x: Invoc, y: Invoc) : bool;

/**
 * Exported declarations
 */

type History;
var {:layer 0,1} h: History;

function {:inline} History.called(h: History, i: Invoc): bool { _called(h)[i] }
function {:inline} History.returned(h: History, i: Invoc): bool { _returned(h)[i] }
function {:inline} History.pending(h: History, i: Invoc): bool { _called(h)[i] && !_returned(h)[i] }

procedure {:yields} {:layer 0} {:refines "_call"}
History.call(m: Method, args: ArgList) returns ({:linear "this"} this: Invoc);

procedure {:yields} {:layer 0} {:refines "_return"}
History.return({:linear_in "this"} this: Invoc, rets: ArgList);

/**
 * Internal declarations
 */

function _called(h: History): [Invoc] bool;
function _returned(h: History): [Invoc] bool;

procedure {:atomic} {:layer 1} _call(m: Method, args: ArgList)
  returns ({:linear "this"} this: Invoc)
  modifies h;
{
  var hh: History;
  var rets: ArgList;

  assume Invoc.match(this, m, args, rets);
  assume (forall i: Invoc :: hb(i, this) ==> _returned(h)[i]);
  assume !_called(h)[this];
  assume !_returned(h)[this];
  assume _called(hh) == _called(h)[this := true];
  assume _returned(hh) == _returned(h);
  h := hh;
  assume _called(h)[this];  // TODO doesn't this follow from above?
}

procedure {:atomic} {:layer 1} _return({:linear_in "this"} this: Invoc, rets: ArgList)
  modifies h;
{
  var hh: History;
  var m: Method;
  var args: ArgList;

  assume Invoc.match(this, m, args, rets);

  // XXX this is supposed to cover for a mysterious problem in Invoc.match
  assume rets == Invoc.rets(this);

  assume _called(hh) == _called(h);
  assume _returned(hh) == _returned(h)[this := true];
  h := hh;
  assume _returned(h)[this];  // TODO doesn't this follow from above?
}
