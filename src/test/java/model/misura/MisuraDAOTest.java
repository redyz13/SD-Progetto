package model.misura;

import model.acquisto.AcquistoBean;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import javax.sql.DataSource;
import java.lang.reflect.Method;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.Collection;
import java.util.Iterator;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.Mockito.*;

class MisuraDAOTest {

    private MisuraDAO dao;

    private DataSource dsMock;
    private Connection connMock;
    private PreparedStatement psMock;
    private ResultSet rsMock;

    @BeforeEach
    void setup() throws Exception {
        dsMock = mock(DataSource.class);
        connMock = mock(Connection.class);
        psMock = mock(PreparedStatement.class);
        rsMock = mock(ResultSet.class);

        dao = new MisuraDAO(dsMock);

        when(dsMock.getConnection()).thenReturn(connMock);
        when(connMock.prepareStatement(anyString())).thenReturn(psMock);
        when(psMock.executeUpdate()).thenReturn(1);
        when(psMock.executeQuery()).thenReturn(rsMock);
    }

    // -------- Test doSave() --------

    // {misura_valida, db_ok}
    @Test
    void doSave_ok_setsAllParamsAndExecutes() throws Exception {
        MisuraBean m = mock(MisuraBean.class);
        when(m.getIDMaglietta()).thenReturn(10);
        when(m.getTaglia()).thenReturn("M");
        when(m.getQuantita()).thenReturn(3);

        dao.doSave(m);

        verify(psMock).setInt(1, 10);
        verify(psMock).setString(2, "M");
        verify(psMock).setInt(3, 3);
        verify(psMock).executeUpdate();
    }

    // {misura_valida, db_exception}
    @Test
    void doSave_dbException_propagatesSQLException() throws Exception {
        when(dsMock.getConnection()).thenThrow(new SQLException("db fail"));

        MisuraBean m = mock(MisuraBean.class);
        when(m.getIDMaglietta()).thenReturn(10);
        when(m.getTaglia()).thenReturn("M");
        when(m.getQuantita()).thenReturn(3);

        assertThrows(SQLException.class, () -> dao.doSave(m));
    }

    // -------- Test doUpdate() --------

    // {misura_valida, db_ok}
    @Test
    void doUpdate_ok_setsAllParamsAndExecutes() throws Exception {
        MisuraBean m = mock(MisuraBean.class);
        when(m.getQuantita()).thenReturn(5);
        when(m.getIDMaglietta()).thenReturn(10);
        when(m.getTaglia()).thenReturn("L");

        dao.doUpdate(m);

        verify(psMock).setInt(1, 5);
        verify(psMock).setInt(2, 10);
        verify(psMock).setString(3, "L");
        verify(psMock).executeUpdate();
    }

    // {misura_valida, db_exception}
    @Test
    void doUpdate_dbException_propagatesSQLException() throws Exception {
        when(dsMock.getConnection()).thenThrow(new SQLException("db fail"));

        MisuraBean m = mock(MisuraBean.class);
        when(m.getQuantita()).thenReturn(5);
        when(m.getIDMaglietta()).thenReturn(10);
        when(m.getTaglia()).thenReturn("L");

        assertThrows(SQLException.class, () -> dao.doUpdate(m));
    }

    // -------- Test doUpdateUtente() --------

    // {acquisto_valido, taglia_valida, db_ok}
    @Test
    void doUpdateUtente_ok_setsAllParamsAndExecutes() throws Exception {
        AcquistoBean a = mock(AcquistoBean.class);
        when(a.getQuantita()).thenReturn(2);
        when(a.getIDMaglietta()).thenReturn(10);

        dao.doUpdateUtente(a, "S");

        verify(psMock).setInt(1, 2);
        verify(psMock).setInt(2, 10);
        verify(psMock).setString(3, "S");
        verify(psMock).executeUpdate();
    }

    // {acquisto_valido, taglia_valida, db_exception}
    @Test
    void doUpdateUtente_dbException_propagatesSQLException() throws Exception {
        when(dsMock.getConnection()).thenThrow(new SQLException("db fail"));

        AcquistoBean a = mock(AcquistoBean.class);
        when(a.getQuantita()).thenReturn(2);
        when(a.getIDMaglietta()).thenReturn(10);

        assertThrows(SQLException.class, () -> dao.doUpdateUtente(a, "S"));
    }

    // -------- Test doRetrieveAll() --------

    // {id_valido, rs_piu_righe, db_ok}
    @Test
    void doRetrieveAll_dueRighe_valuesAreMapped() throws Exception {
        AtomicInteger nextCalls = new AtomicInteger(0);
        when(rsMock.next()).thenAnswer(inv -> {
            int c = nextCalls.incrementAndGet();
            if (c == 1) return true;
            if (c == 2) return true;
            if (c == 3) return false;
            throw new AssertionError("too many next calls");
        });

        when(rsMock.getInt("IDMaglietta")).thenReturn(10, 10);
        when(rsMock.getString("taglia")).thenReturn("S", "M");
        when(rsMock.getInt("quantita")).thenReturn(4, 7);

        Collection<MisuraBean> res = dao.doRetrieveAll(10);

        assertEquals(2, res.size());

        Iterator<MisuraBean> it = res.iterator();
        MisuraBean m1 = it.next();
        MisuraBean m2 = it.next();

        assertEquals(10, m1.getIDMaglietta());
        assertEquals("S", m1.getTaglia());
        assertEquals(4, m1.getQuantita());

        assertEquals(10, m2.getIDMaglietta());
        assertEquals("M", m2.getTaglia());
        assertEquals(7, m2.getQuantita());

        verify(psMock).setInt(1, 10);
        verify(psMock).executeQuery();
    }

    // {id_valido, rs_vuoto, db_ok}
    @Test
    void doRetrieveAll_zeroRighe_returnsEmpty() throws Exception {
        when(rsMock.next()).thenReturn(false);

        Collection<MisuraBean> res = dao.doRetrieveAll(10);

        assertNotNull(res);
        assertTrue(res.isEmpty());

        verify(psMock).setInt(1, 10);
        verify(psMock).executeQuery();
    }

    // {db_exception}
    @Test
    void doRetrieveAll_dbException_propagatesSQLException() throws Exception {
        when(dsMock.getConnection()).thenThrow(new SQLException("db fail"));
        assertThrows(SQLException.class, () -> dao.doRetrieveAll(10));
    }

    // -------- Test setMisura() --------

    // {rs_valori_normali}
    @Test
    void setMisura_ok_setsAllFields() throws Exception {
        when(rsMock.getInt("IDMaglietta")).thenReturn(10);
        when(rsMock.getString("taglia")).thenReturn("M");
        when(rsMock.getInt("quantita")).thenReturn(6);

        Method m = MisuraDAO.class.getDeclaredMethod("setMisura", ResultSet.class, MisuraBean.class);
        m.setAccessible(true);

        MisuraBean out = new MisuraBean();
        m.invoke(dao, rsMock, out);

        assertEquals(10, out.getIDMaglietta());
        assertEquals("M", out.getTaglia());
        assertEquals(6, out.getQuantita());
    }

    // {rs_exception}
    @Test
    void setMisura_rsThrows_wrapsInvocationCauseAsSQLException() throws Exception {
        when(rsMock.getInt("IDMaglietta")).thenThrow(new SQLException("boom"));

        Method m = MisuraDAO.class.getDeclaredMethod("setMisura", ResultSet.class, MisuraBean.class);
        m.setAccessible(true);

        Exception ex = assertThrows(Exception.class, () -> m.invoke(dao, rsMock, new MisuraBean()));
        assertNotNull(ex.getCause());
        assertInstanceOf(SQLException.class, ex.getCause());
        assertTrue(ex.getCause().getMessage().contains("boom"));
    }
}
