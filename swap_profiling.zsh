#!/bin/zsh

#grep -l '(* Set Ltac Profiling. *)' | xargs sed -i 's/(* Set Ltac Profiling. *)/Set Ltac Profiling./g'
#grep -l '(* Show Ltac Profile. *)' | xargs sed -i 's/(* Show Ltac Profile. *)/Show Ltac Profile./g'

grep -l 'Set Ltac Profiling.' protocols/**/*.v | xargs sed -i 's/Set Ltac Profiling./(* Set Ltac Profiling. *)/g'
grep -l 'Show Ltac Profile.' protocols/**/*.v | xargs sed -i 's/Show Ltac Profile./(* Show Ltac Profile. *)/g'
