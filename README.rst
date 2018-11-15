======
Carbon
======

Carbon is a verification-condition-generation-based verifier for
`the Viper intermediate verification language <https://bitbucket.org/viperproject/silver>`_.

`The Viper project <http://www.pm.inf.ethz.ch/research/viper.html>`_ is developed by the
`Programming Methodology <http://www.pm.inf.ethz.ch/>`_ group
at ETH Zurich.

See `the documentation wiki <https://bitbucket.org/viperproject/documentation/>`_ for instructions on how to try out or install the Viper tools.

|

Installation Instructions:
--------------------------

* Clone `silver <https://bitbucket.org/viperproject/silver/>`_ repository in your computer.
* Clone **carbon** (this repository) in your computer, in a separate directory.
* From within the directory where you installed carbon, create a symbolic link to the directory where you installed silver.
* On Linux/Mac OS X::
 ln -s <relative path to diretory where you installed silver> silver
* On Windows::
 mklink /D silver <relative path to diretory where you installed silver>
* Compile by typing::
 sbt compile