## V1 Proof by Induction

To make the following work:
{% highlight text %}
From X Require Export Y.
{% endhighlight %}

Execute the following command first:
{% highlight text %}
coqc Y.v
{% endhighlight %}

When simplification + reflexivity does not work, try case analysis (`destruct`).

When case analysis does not work, try proof by induction (`induction`).

`assert` can be use to prove things using the variables of the main proof. `assert` is useful because it is closure-aware.

{% comment %}
Open quests:
{% endcomment %}
