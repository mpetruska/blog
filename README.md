## Welcome

Probably every enthusiastic software engineer
develops ideas that are worth sharing (possibly
to avoid [reinventing the square wheel][square]).

This blog is [my][cv] collection of thoughts and
their rationale (or in some cases mathematical proof).

[cv]:     https://mpetruska.github.io/cv
[square]: https://en.wikipedia.org/wiki/Anti-pattern

### Posts

<ul>
  {% for post in site.posts %}
    <li>
      <a href="{{ post.url }}">{{ post.title }}</a>
      {{ post.excerpt }}
    </li>
  {% endfor %}
</ul>
