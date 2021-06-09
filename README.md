The CFG configuration format is a text format for configuration files which is similar to, and a superset of, the JSON format. It dates from [2008](https://wiki.python.org/moin/HierConfig) and has the following aims:

* Allow a hierarchical configuration scheme with support for key-value mappings and lists.
* Support cross-references between one part of the configuration and another.
* Provide the ability to compose configurations (using include and merge facilities).
* Provide the ability to access real application objects safely.

It overcomes a number of drawbacks of JSON when used as a configuration format:

* JSON is more verbose than necessary.
* JSON doesn’t allow comments.
* JSON doesn’t allow trailing commas in lists and mappings.

Installation
============
The package can be installed for use from the [D package registry](https://code.dlang.org) using the package name `cfg-lib`.

Exploration
============
To explore CFG functionality for D, we use the `drepl` Read-Eval-Print-Loop (REPL), which is available from [here](https://github.com/vsajip/drepl). Once installed, you can invoke a shell using
```
$ drepl
```

Getting Started with CFG in D
=============================
A configuration is represented by an instance of the `Config` struct. The constructor for this class can be passed a filename or a stream which contains the text for the configuration. The text is read in, parsed and converted to an object that you can then query. A simple example:

```
a: 'Hello, '
b: 'world!'
c: {
  d: 'e'
}
'f.g': 'h'
christmas_morning: `2019-12-25 08:39:49`
home: `$HOME`
foo: `$FOO|bar`
```

Loading a configuration
=======================
The configuration above can be loaded as shown below. In the REPL shell:

```
D> import config;
config
D> Config cfg; shared static this() { cfg = null; }
cfg
D> cfg = new Config("test0.cfg")
Config(test0.cfg)
```
The one-time-per-session dance with `shared static this()` is currently needed due to a limitation of `drepl`.

Access elements with keys
=========================
Accessing elements of the configuration with a simple key is just like using an associative array:

```
D> cfg["a"]
Hello,
D> cfg["b"]
world!
```
You can see the types and values of the returned objects are as expected.

Access elements with paths
==========================
As well as simple keys, elements  can also be accessed using `path` strings:
```
D> cfg["c.d"]
e
```
Here, the desired value is obtained in a single step, by (under the hood) walking the path `c.d` – first getting the mapping at key `c`, and then the value at `d` in the resulting mapping.

Note that you can have simple keys which look like paths:
```
D> cfg["f.g"]
h
```
If a key is given that exists in the configuration, it is used as such, and if it is not present in the configuration, an attempt is made to interpret it as a path. Thus, `f.g` is present and accessed via key, whereas `c.d` is not an existing key, so is interpreted as a path.

Access to date/time objects
===========================
You can also get native date/time objects from a configuration, by using an ISO date/time pattern in a `backtick-string`:
```
D> cfg["christmas_morning"]
2019-Dec-25 08:39:49
```
Access to environment variables
===============================

To access an environment variable, use a `backtick-string` of the form `$VARNAME`:
```
D> cfg["home"]
/home/vinay
```
You can specify a default value to be used if an environment variable isn’t present using the `$VARNAME|default-value` form. Whatever string follows the pipe character (including the empty string) is returned if `VARNAME` is not a variable in the environment.
```
D> cfg["foo"]
bar
```
For more information, see [the CFG documentation](https://docs.red-dove.com/cfg/index.html).
