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
      "agda --html --html-dir=html --html-highlight=code --css=Agda.css src/readme.lagda.md"
    );

    // Generate template
    const templateSource = await fs.readFile("./web/template.html", "utf8");
    const template = Handlebars.compile(templateSource);

    // Generate Files
    const files = await fs.readdir("./html/");
    for (const file of files) {
      // Read file
      const md = await fs.readFile(`./html/${file}`, "utf8");

      // Parse File
      const conv = new showdown.Converter({ metadata: true });
      const html = conv.makeHtml(md);
      const metadata = conv.getMetadata(); // returns metadata of last conv

      // Write
      await fs.writeFile(
        `./html/${file.slice(0, file.length - 3)}.html`,
        template({ body: html, title: metadata.title })
      );
    }

    // Paste styles.css
    await exec("cp ./web/styles.css ./html/styles.css");
  } catch (e) {
    console.error(e);
  }
}

build();
