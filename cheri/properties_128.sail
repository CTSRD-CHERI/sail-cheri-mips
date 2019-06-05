$property
function prop_inc_bounds_eq(c : Capability, delta : bits(64)) -> bool = {
  let (representable, c') = incCapOffset(c, delta) in
  ~(representable) | capBoundsEqual(c, c')
}

$property
function prop_set_bounds_exact(c : Capability, base' : bits(64), top' : bits(65)) -> bool = {
  let (exact, c') = setCapBounds(c, base', top');
  let (base'', top'') = getCapBounds(c');
  ~(exact) | (base'' == unsigned(base') & top'' == unsigned(top'))
}

$property
function prop_set_bounds_mono(c_bits : CapBits, len' : bits(64)) -> bool =
  let c = capBitsToCapability(true, c_bits) in
  let (base, top) = getCapBounds(c) in
  let base' = getCapCursor(c) in
  let top' = base' + unsigned(len') in
  let (_, c') = setCapBounds(c, to_bits(64, base'), to_bits(65, top')) in
  let (base'', top'') = getCapBounds(c') in
  if (base <= base' & top' <= top) then (base <= base'' & top'' <= top) else true
