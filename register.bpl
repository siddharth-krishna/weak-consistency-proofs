// Simple concurrent variable with get and put methods

var {:layer 0,2} x: int;


// ---------- Basic primitives: read, cas, etc

procedure {:atomic} {:layer 1,2} cas_spec(ole: int, new: int) returns (succ: bool)
  modifies x;
{
  if (x == ole) {
    x := new;
    succ := true;
  } else {
    succ := false;
  }
}

procedure {:yields} {:layer 0} {:refines "cas_spec"} cas(ole: int, new: int)
  returns (succ: bool);

procedure {:atomic} {:layer 1,2} write_spec(new: int)
  modifies x;
{
  x := new;
}

procedure {:yields} {:layer 0} {:refines "write_spec"} write(new: int);

procedure {:atomic} {:layer 1,2} read_spec() returns (v: int)
{
  v := x;
}

procedure {:yields} {:layer 0} {:refines "read_spec"} read() returns (v: int);


// ---------- Actual methods

procedure {:atomic} {:layer 2} put_spec(new: int) returns (ole: int)
  modifies x;
{
  ole := x;
  x := new;
}

procedure {:yields} {:layer 1} {:refines "put_spec"} put(new: int) returns (ole:int)
{
  var succ: bool;

  yield;
  call ole := read();
  yield;
  
  while (true) {
    call succ := cas(ole, new);

    if (succ) {
      yield;
      return;
    }
    yield;
  }
  yield;
}


procedure {:atomic} {:layer 2} get_spec() returns (v: int)
{
  v := x;
}

procedure {:yields} {:layer 1} get() returns (v: int)
{
  yield;
  call v := read();
  yield;
}
