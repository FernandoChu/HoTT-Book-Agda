const Handlebars = require("handlebars");
const fs = require("fs").promises;
const showdown = require("showdown");

const util = require("util");
const exec = util.promisify(require("child_process").exec);

async function build() {
  try {
    // Typecheck and generate md
    await exec("rm -rf html");
    await exec(
      "agda --html --html-dir=html --html-highlight=code --css=Agda.css src/index.lagda.md"
    );

    // Generate template
    const templateSource = await fs.readFile("./web/template.html", "utf8");
    const template = Handlebars.compile(templateSource);

    // Generate Files
    const files = await fs.readdir("./html/");
    for (const file of files) {
      // Read file
      const fileContents = await fs.readFile(`./html/${file}`, "utf8");

      if (file === "Agda.Primitive.html") {
        await fs.writeFile(
          `./html/${file}`,
          template({
            body: `<pre class="Agda">${fileContents}</pre>`,
            title: "Agda Primitives",
            backToIndex: `<a href="index.html">Back to index</a>`,
          })
        );
      } else {
        // Parse File
        const conv = new showdown.Converter({ metadata: true });
        const html = conv.makeHtml(fileContents);
        const metadata = conv.getMetadata(); // returns metadata of last conv

        // Write
        await fs.writeFile(
          `./html/${file.slice(0, file.length - 3)}.html`,
          template({
            body: html,
            title: metadata.title,
            backToIndex: metadata.isIndex
              ? null
              : `<a href="index.html">Back to index</a>`,
          })
        );
      }
    }

    // Paste styles.css
    await exec("cp ./web/styles.css ./html/styles.css");
  } catch (e) {
    console.error(e);
  }
}

build();
