function selezione() {
  sessionStorage.setItem("radioNo",JSON.stringify({"radioNo":"checked"}))
  let selezione = document.querySelector('input[name="selezione"]:checked').value;
  if (selezione === "no") {
    document.getElementById("newLine").hidden=true;
    document.getElementById("labelGrafica").hidden=true;
    document.getElementById("fileInput").hidden=true;
  }
  else {
    document.getElementById("newLine").hidden=false;
    document.getElementById("labelGrafica").hidden=false;
    document.getElementById("fileInput").hidden=false
  }
}

function setRadio() {
   let data = sessionStorage.getItem('radioNo');
   if (JSON.parse(data).radioNo === 'checked'){
     document.getElementById("radioNo").checked = true;
 }
}