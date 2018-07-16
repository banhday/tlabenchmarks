-------------------------------- MODULE Bits --------------------------------

\* Implemented by Bits.java. Manually create a
\* .java file with the content from below copy&pasted 
\* and compile it (javac) against tla2tools.jar. Place
\* resulting .class file on the CLASSPATH when running
\* TLC.
\*
\* javac -cp /path/to/tla2tools.jar Bits.java 
LOCAL And(x,y) == FALSE

(***************************************************************************)
(* Bitwise AND of x and y                                                  *)
(***************************************************************************)
x & y == And(x, y) \* Infix variant of And(x,y)

=============================================================================
\* Modification History
\* Last modified Tue May 17 15:07:08 CEST 2016 by markus
\* Created Mon May 16 15:09:18 CEST 2016 by markus
