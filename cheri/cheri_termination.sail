val execute_measure : ast -> int
function execute_measure(instr) =
  match instr {
    CLCNT(cd,cb,rt) => 1,
    _ => 0
  }
termination_measure execute(i) = execute_measure(i)
