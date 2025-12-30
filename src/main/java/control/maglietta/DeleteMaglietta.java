package control.maglietta;

import model.maglietta.MagliettaDAO;

import javax.servlet.ServletException;
import javax.servlet.annotation.WebServlet;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import java.io.IOException;
import java.sql.SQLException;

@WebServlet("/DeleteMaglietta")
public class DeleteMaglietta extends HttpServlet {

    @Override
    protected void doPost(HttpServletRequest req, HttpServletResponse resp)
            throws ServletException, IOException {

        int ID;

        try {
            ID = Integer.parseInt(req.getParameter("ID"));
        } catch (NumberFormatException e) {
            req.getRequestDispatcher("/pages/errorpage.jsp").forward(req, resp);
            return;
        }

        MagliettaDAO magliettaDAO = new MagliettaDAO();

        try {
            if (!magliettaDAO.deleteMaglietta(ID)) {
                req.getRequestDispatcher("/pages/errorpage.jsp").forward(req, resp);
                return;
            }
        } catch (SQLException e) {
            req.getRequestDispatcher("/pages/errorpage.jsp").forward(req, resp);
            return;
        }

        req.getRequestDispatcher("catalogoAdmin.jsp").forward(req, resp);
    }
}
