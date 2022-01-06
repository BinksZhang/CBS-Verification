# 一种基于分离逻辑的块云存储系统验证工具

在交互式定理证明工具Coq中，我们实现了一个针对块云存储系统（CBS）的验证工具。它具备分离逻辑的关键特性，尤其能支持对CBS程序进行局部推导。

对应实际CBS的主从式架构，工具将CBS细分为两个存储层级:文件层、块层。通过整合内部层级的状态和操作，工具支持表示和验证对实际CBS中的各项数据操作。

## 工具中证明系统的构建环节

事实上，我们基于分离逻辑，实现了一个关于CBS的证明系统。它涉及到构建建模语言、断言语言、分离逻辑三元组和推理规则等环节。这些环节与工程文件的对应关系如下：

- 建模语言——Language.v
- 断言语言——内部堆谓词（InnerPre.v）+ CBS堆谓词（Himpl.v）
- CBS分离逻辑三元组和推理规则——Rules.v
- 验证实例——Example.v 

此外，还有一些支持工具开发的原有库文件

- TLC：Coq标准库
- Fmap.v：有限映射
- Var.v: 变量符号

工具的实现共涉及3325行代码，其中包括51条定义，242条引理。

最后，工具还提供了7个实例的证明，它们分别为：拷贝数据块、移动数据块、清除文件、读取文件内容、向文件尾部添加一个数据块、创建文件、拷贝文件。以此说明了工具对CBS程序的表示和推理能力。

## 工具的开发环境

本工具的开发环境为：

- 操作系统：Windows 10
- Coq版本：Coq 8.8.0
- IDE : vscode

## 工具的编译方式

#### 1. 下载压缩包文件到本地，并解压缩

​	**注意:** 解压缩后的文件路径中，不可以有中文！！！

##### 安装Coq 8.8.0并配置环境变量

- 安装Coq

​	下载地址：

​	https://github.com/coq/coq/releases/download/V8.8.0/coq-8.8.0-installer-windows-x86_64.exe

完成安装后，需要配置Coq的环境变量：

- 打开环境变量设置

<img src="image\image-20210724145029025.png" alt="avatar" style="zoom:35%;" />

- 在系统变量的Path一栏中，添加Coq的安装路径。

<img src="image\image-20210724145233682.png" alt="avatar" style="zoom:35%;" />

<img src="image\image-20210724155616354.png" alt="avatar" style="zoom:50%;" />

#### 2. 安装Chocolatey软件管理器

​	以**管理员方式**打开powershell，

<img src="image\1d2efe194fd9a4fd38253d08c9f8ba2.jpg" alt="avatar" style="zoom:50%;" />

​	粘贴如下代码：

` Set-ExecutionPolicy Bypass -Scope Process -Force; iex ((New-Object System.Net.WebClient).Downloa
dString('https://chocolatey.org/install.ps1')) `

注：如果出现如下形式的报错：

` “... 使用“1”个参数调用“DownloadString”时发生异常:“请求被中止: 未能创建 SSL/TLS 安全通道...”`

​	请先在Powershell中，粘贴以下代码设定协议

` [Net.ServicePointManager]::SecurityProtocol = [Net.SecurityProtocolType]::Tls12 `

再粘贴安装代码。开始安装时界面如下

<img src="image\c05934f169e1ab1bc222dcad90313c2.png" alt="avatar" style="zoom:50%;" />

#### 3. 在Cmder中安装make编译工具

-  安装终端模拟器Cmder（**需要安装full版本**）

   下载地址：https://cmder.net/

​	cmder解压后即可使用，建议和本工具文件解压到同一个根目录中。

<img src="image\image-20210724160349470.png" alt="avatar" zoom=90% />

- 以**管理员方式**打开cmder，粘贴如下指令，安装make编译工具：

  `choco install mingw`

#### 3. 安装完成后，在cmder中进入解压后的工具文件夹，输入make即可开始编译

<img src="image\image-20210724145814033.png" alt="avatar" style="zoom:50%;" />



最后，直接双击*.v文件，可以用CoqIDE审阅相应的代码。

（如果此时Coq崩溃，说明路径中有中文）

<img src="image\image-20210724150102388.png" alt="avatar" style="zoom:80%;" />

