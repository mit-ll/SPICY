# Questions about the real-world model for Ben Kaiser during phone conversation on 9/12.

* Why are keys both environments and return arguments?
  * not clear 
  * why choose one or the other? ask Adam
* Can you sketch out the step relationship, especially the unwritten commands (Return, Bind, BindSymKey, BindAsymKey, Barrier). I'd like to talk at the level of operational semantics.
  * barrier: adjust key stuff ?
  * 
* Why is the (global?) message heap an ```fmap var message ```instead of ```list (var * message)``` to prevent overwrites?
  * not the global heap


# General
* keys are native objects
* talk to Dan Uten (LOCKMA) or David Wilson (theortical mostly) 
