import cpp

/**
 * @name Use after free
 * @description Finds potential use-after-free vulnerabilities in the specified file.
 * @kind problem
 * @problem.severity error
 * @id cpp/use-after-free
 * @tags security
 */

predicate isTargetFile(Function f) {
  f.getFile().getRelativePath() = "src/pkcs15init/pkcs15-authentic.c"
}

class UseAfterFreeFunction extends Function {
  UseAfterFreeFunction() { isTargetFile(this) }

  predicate hasUseAfterFree() {
    exists(VariableAccess freeVar, FunctionCall freeCall |
      freeVar = freeCall.getArgument(0) and
      freeCall.getTarget().hasName("free") and
      freeVar.getAChild*() = this.getAChild*() and
      exists(VariableAccess useVar |
        useVar.getTarget() = freeVar.getTarget() and
        useVar.getStartLine() > freeCall.getEndLine()
      )
    )
  }

  predicate hasFreeBeforeUse() {
    exists(FunctionCall freeCall, FunctionCall useCall |
      freeCall.getTarget().hasName("free") and
      useCall.getTarget().getFile() = this.getFile() and
      useCall.getStartLine() > freeCall.getEndLine() and
      freeCall.getArgument(0) = useCall.getArgument(0)
    )
  }
}

from UseAfterFreeFunction uf
where uf.hasUseAfterFree() or uf.hasFreeBeforeUse()
select uf, "Potential use-after-free vulnerability detected in " + uf.getName()