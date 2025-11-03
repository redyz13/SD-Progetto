//Switch Log In and Sign Up Forms

function changeForm(str) {
  let lForm = document.getElementById("lform");
  let sForm = document.getElementById("sform");

  if (str === "Sign Up") {
    lForm.style.display = "none";
    sForm.style.display = "block";
  } else {
    sForm.style.display = "none";
    lForm.style.display = "block";
  }
}