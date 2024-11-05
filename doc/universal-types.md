# Special Treatment of Capabilities for Universal Types

System Capless supports precise curried captures. For instance, given the following function:
```scala
() => () =>
  logger.info("Hello, World!")
  () =>
    file.write("Hello Again!")
```
its type will be
```scala
() ->{} () ->{logger} () ->{file} Unit
```
but not
```scala
() ->{logger,file} () ->{logger,file} () ->{file} Unit
```
The latter type is the old behavior: it is how CC<:box works.

Additionally, given a variable `x`, the set `{x}` is a subcapture of the capabilities on the *first* arrow along the spine, but not all captures along the spine. For instance, given `x : () ->{} () ->{logger} () ->{file} Unit`, we have `{x} <: {}`. `x` is considered pure! Together with a mechanism called environment avoidance, this feature enables precise usage tracking.

Unfortunately these mechanisms are causing us problems, among which one is that the translation from System Cappy to System Capless breaks. This note first presents the problem, and then proposes a revision to the system as a solution.

This problem is better understood by inspecting an example.
Given a function `f` of type `(zs: List[() => Unit]) ->{io} Unit` in System Cappy, consider the following application form:
```
f(xs)
```
where we assume `xs` is some variable with an appropriate type. Here `io` is a(n) (IO) capability in the scope.

The translated type of `f` will be `[C^] ->{} (zs: List[() ->{C^} Unit] ->{io} Unit)`. Notice that before the translation, we have `{f} <: {io}` (which means `f` is considered impure) but afterwards, we can derive `{f} <: {}`, which means `f` is pure! This may seem fine, as a purer function can be better. But essentially, what happens here is that `f` no longer stands for the `{io}` effect the function can perform. We wasted a name. To see how it can be a problem, consider the translated term:
```
let z1 = f[{...}] in z1(xs)
```
We can verify that the best `cv` we could assign to this term is `{io,xs}`. But previously it is `{f,xs}`. It is slightly larger! This turns out to be a devastating problem which breaks type preservation completely with regards to translation.

We have argued that the essential cause of this problem is the "waste" of names. In fact, for any universal types, either being polymorphic over types or capture sets, the effect will only happen on the subsequent arrows, but not on the first one. Most universal quantifiers are followed immediately by a term abstraction. The implication is that given a variable `x` of such types, `x` is always pure: it does not stand for any effect induced by the function.

Therefore, we propose to revise the system by letting a capability of a universal type stand for the captures of not only the first but also the second arrow. Specifically, given
```
f : [C^] ->{} (zs: List[() ->{C^} Unit]) ->{io} Unit
```
in the context, we have `{f} <: {io}`. And when typing the variable `f`, we replace the captures on the first two arrows with `f`:
```
[C^] ->{f} (zs: List[() ->{C^} Unit]) ->{f} Unit
```
This way, any capability `x` of a universal type stands for the effects from the first two arrows along the spine.
