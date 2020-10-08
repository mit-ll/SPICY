# Extracted code and effect handlers.

## Print to the screen interpreter

The simplest interpreter merely prints out the commands to the screen
rather than performing any meaningful interpretation.  This is by far
the least sophisticated implementation, but maybe should be generalized
a bit to support simple printing of *any* extracted protocol.  For now,
it only does the _Simple Ping Protocol_.

You can run by invoking:

```
stack exec printProto
```

## Execute users in threads interpreter

This is a single process interpreter, which uses shared memory to
pass messages.  Effects are actually run, but messaging isn't particularly
meaningful.  It currently only runs the _Simple Ping Protocol_.

You can run by invoking:

```
stack exec runProto
```

## Multi process messaging via sockets interpreter

The most sophisticated harness.  Runs each user in a separate process,
and uses sockets for communication of messages.  It currently supports
both the _Simple Ping Protocol_ and the _Share Secret Protocol_.  Choices
are made using command line options:

* **user** -- userid of user to run in this shell
* **proto** -- which protocol to run, either "ping" or "sharesec"
* **advPort** -- optional integer for port to run the adversary on (100 is a good choice)

This protocol comes with a hand-rolled adversary, which has its own command
line options:

* **port** -- port to run the adversary on (should match advPort from above)
* **usrs** -- userid to send messages to - can be passed multiple times to list more than one user

Example run script for this interpreter.  Note each line below is meant to be
invoked from different shells:

```
stack exec runProtoSplit -- --proto sharesec --advPort 100 --user 1
stack exec runProtoSplit -- --proto sharesec --advPort 100 --user 0
stack exec adversary -- usrs 0 --usrs 1 --port 100
```

Note, there is a race condition in setting up ports and sending to them, so even
though some thoughtful thread delays are place within the code, for the share secret
protocol, the commands shoule be executed in the above order.
