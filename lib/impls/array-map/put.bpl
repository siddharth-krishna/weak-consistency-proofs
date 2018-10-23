procedure {:yields} {:layer 1} {:refines "put_spec"} put(args: ArgList)
  returns (rets: ArgList)
  requires {:layer 1} tableInv(table, tabLen, tabvis, abs, lin, vis, h);
  requires {:layer 1} 0 <= args[0] && args[0] < tabLen;
  ensures {:layer 1} tableInv(table, tabLen, tabvis, abs, lin, vis, h);
{
  var {:linear "this"} this: Invoc;
  var {:layer 1} my_vis: Set;

  var k: int;
  var v: int;

  yield; assert {:layer 1} tableInv(table, tabLen, tabvis, abs, lin, vis, h);
  call this := History.call(Map.put, args);
  yield; assert {:layer 1} tableInv(table, tabLen, tabvis, abs, lin, vis, h) && History.pending(h, this);

  k := args[0];
  v := args[1];

  call writeTable(k, v);

  call intro_add_tabvis(k, this);
  call my_vis := intro_read_tabvis_range(0, tabLen);
  call intro_write_vis(this, my_vis);
  call intro_writeAbs(k, v);
  call intro_writeLin(this);

  yield; assert {:layer 1} tableInv(table, tabLen, tabvis, abs, lin, vis, h)
    && History.pending(h, this) && Seq.elem(this, lin);
  call History.return(this, rets);
  yield; assert {:layer 1} tableInv(table, tabLen, tabvis, abs, lin, vis, h);
}
