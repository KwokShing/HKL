# HKL 本地网页渲染器

从仓库 `py/` 目录发现 Python Spider，并通过统一网页调用首页、分类、搜索、详情和播放接口。

## Windows 启动

```cmd
cd web
py -m venv .venv
.venv\Scripts\python -m pip install -r requirements.txt
.venv\Scripts\python server.py
```

浏览器访问 <http://127.0.0.1:8000>。

> 插件是可执行 Python 代码，只应加载你已审查并信任的本地文件。渲染器只绑定本机回环地址，但无法把插件本身变成安全代码。不同插件依赖和返回结构并不完全一致，页面会显示具体兼容性错误。
