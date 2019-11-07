# Setup

To install this library on your system, first clone this repository; we will
refer to the location of this repository as `<basics-dir>`.
Next, follow the instructions here:

https://agda.readthedocs.io/en/v2.5.4/tools/package-system.html

Specifically, you need to:

- Create (or add to) the Agda library index file on your system located at
  `~/.agda` with this new line:

      <basics-dir>/basics.agda-lib

- Create (or add to) your Agda project file located at `<project>/.agda-lib`
  with this content:

      name: <project-name>
      depend: basics

***Windows Users***: instead of `~/.agda`, you should use the path
`C:\Users\USERNAME\AppData\Roaming\agda`.
