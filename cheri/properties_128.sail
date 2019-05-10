/*$counterexample
function prop_inc_bounds_eq(c : Capability, delta : bits(64)) -> bool = {
  let (representable, c') = incCapOffset(c, delta) in
  ~(representable) | capBoundsEqual(c, c')
}*/

$property
function prop_set_bounds_exact(c : Capability, base' : bits(64), top' : bits(65)) -> bool = {
  let (exact, c') = setCapBounds(c, base', top');
  let (base'', top'') = getCapBounds(c');
  ~(exact) | (base'' == unsigned(base') & top'' == unsigned(top'))
}

/*$property
function prop_set_bounds_mono(c : Capability, base' : bits(64), top' : bits(65)) -> bool = {
  let (base, top) = getCapBounds(c);
  let (_, c') = setCapBounds(c, base', top');
  let (base'', top'') = getCapBounds(c');
  if (base <= unsigned(base') & unsigned(top') <= top) then (base <= base'' & top'' <= top) else true
}*/
