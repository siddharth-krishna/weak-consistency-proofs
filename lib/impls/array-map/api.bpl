procedure {:atomic} {:layer 2} put_spec(args: ArgList) returns (rets: ArgList)
  modifies abs, lin, vis;
{
  var {:linear "this"} this: Invoc;
  var my_vis: Set;

  assume Invoc.match(this, Map.put, args, rets);

  lin := Seq.append(lin, this);
  vis[this] := my_vis;
  assume Consistency.complete(lin, vis, this);

  // Put satisfies its functional spec
  // FIXME
  abs[args[0]] := args[1];
  // assume Map.spec.put(my_vis, lin, args);
}

procedure {:atomic} {:layer 2} get_spec(args: ArgList) returns (rets: ArgList)
  modifies lin, vis;
{
  var {:linear "this"} this: Invoc;
  var my_vis: Set;

  assume Invoc.match(this, Map.get, args, rets);

  lin := Seq.append(lin, this);
  vis[this] := my_vis;
  assume Consistency.complete(lin, vis, this);

  // Get satisfies its functional spec
  assume Map.spec.get(my_vis, lin, args, rets);
}

procedure {:atomic} {:layer 2} contains_spec(args: ArgList) returns (rets: ArgList)
  modifies lin, vis;
{
  var {:linear "this"} this: Invoc;
  var my_vis: Set;

  assume Invoc.match(this, Map.contains, args, rets);

  // FIXME this is a bit special...
  assume tabLen - 1 == Map.key(this);

  lin := Seq.append(lin, this);
  vis[this] := my_vis;
  assume Consistency.monotonic(lin, vis, this);

  // Contains satisfies its functional spec
  assume Map.spec.contains(my_vis, lin, tabLen, args, rets);
}
