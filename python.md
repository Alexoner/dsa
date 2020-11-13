### Python debug

#### with pdb debugger
pip install options:
-e,--editable <path/url>
	Install a project in editable mode (i.e.  setuptools "develop mode") from a local project path or a VCS url.

	pip install -e .

Set breakpoint by inserting:

    __import__('ipdb').set_trace()

#### code injection

```python
from module_name import SomeClass

def overriddenMethod(self, ...):
    # do something
    pass

def overriddenStaticMethod(...):
    # do something
    pass
SomeClass.someMethod       = overriddenMethod
SomeClass.someStaticMethod = overriddenStaticMethod

# note:
# Single Underscore means internal use names
# Double underscore means name mangling, outside access like this:
SomeClass.__dict__['_SomeClass' + 'double_underscored_names'].__func__(...)

```

#### profiling


cProfile will only show list of functions, without call stack.
For call stack, use [pyinstrument](https://github.com/joerick/pyinstrument), which is a sampling based statistical profiler.

```python
import cProfile
cProfile.run('foo()')
```

```shell
python -m cProfile <script>
```


