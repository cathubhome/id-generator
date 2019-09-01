package com.wujunshen.core.utils;

import java.lang.management.ManagementFactory;
import java.net.InetAddress;
import java.net.NetworkInterface;

/**
 * <p>名称：IdWorker.java</p>
 * <p>描述：分布式自增长ID</p>
 * <pre>
 *     Twitter的 Snowflake　JAVA实现方案
 * </pre>
 * 核心代码为其IdWorker这个类实现，其原理结构如下，我分别用一个0表示一位，用—分割开部分的作用：
 * 1||0---0000000000 0000000000 0000000000 0000000000 0 --- 00000 ---00000 ---000000000000
 * 在上面的字符串中，第一位为未使用（实际上也可作为long的符号位），接下来的41位为毫秒级时间，
 * 然后5位datacenter标识位，5位机器ID（并不算标识符，实际是为线程标识），
 * 然后12位该毫秒内的当前毫秒内的计数，加起来刚好64位，为一个Long型。
 * 这样的好处是，整体上按照时间自增排序，并且整个分布式系统内不会产生ID碰撞（由datacenter和机器ID作区分），
 * 并且效率较高，经测试，snowflake每秒能够产生26万ID左右，完全满足需要。
 * <p>
 * 64位ID (42(毫秒)+5(机器ID)+5(业务编码)+12(重复累加))
 *
 * @author Polim
 */

/**
 *<pre>
 *  Created with IntelliJ IDEA
 *  Author: cathome
 *  Email: 1015726552@qq.com
 *  Time: 2019-09-01 22:43:10
 *  Class: IdWorker
 *  Package: com.wujunshen.core.utils
 *  Description: 利用twitter snowflakes算法实现分布式高效有序ID
 *  Version: 1.0
 *</pre>
 */
public class IdWorker {

    /**
     snowflake的结构如下,64bit(每部分用 - 分开):
     0 - 0000000000 0000000000 0000000000 0000000000 0 - 00000 - 00000 - 000000000000
     ① 最高位的1bit位，由于long基本类型在Java中是带符号的,最高位是符号位,正数是0,负数是1,而id一般是正数,所以最高位是0;
     ② 41bit-时间戳 精确到毫秒级，41位的长度可以使用69年,年T=(1L<<41)/(1000L*60*60*24*365)=69,特别注意41位时间截不是存储当前时间的时间截，而是存储时间截的差值
     ③ 10bit-工作机器id 10位的机器标识，10位的长度最多支持部署1024个节点,包括5位数据中心Id和5位机器Id;
     ④ 12bit-序列号 序列号即一系列的自增id,可以支持同一节点同一毫秒生成多个ID序号
     12位（bit）可以表示的最大正整数是2^{12}-1 = 4095,即同一机器同一时间截（毫秒)内产生的4095个ID序号.
     说明：由于在Java中64bit的整数是long类型,所以在Java中SnowFlake算法生成的id就是long来存储的
     */

    /**
     * 时间起始标记点[开始时间截]，作为基准，一般取系统的最近时间（一旦确定不能变动）
     */
    private final static long TW_EPOCH = 1288834974657L;

    /**
     * 机器标识位数
     */
    private final static long WORKER_ID_BITS = 5L;

    /**
     * 数据中心标识位数
     */
    private final static long DATACENTER_ID_BITS = 5L;

    /**
     * 数据中心ID最大值(下面的移位算法可以迅速计算出N位二进制数所能表示的最大十进制数)
     */
    private final static long MAX_DATA_CENTER_ID = -1L ^ (-1L << DATACENTER_ID_BITS);

    /**
     * 机器ID最大值
     */
    private final static long MAX_WORKER_ID = -1L ^ (-1L << WORKER_ID_BITS);

    /**
     * 毫秒内自增位（序列在snowflake中占的位数）
     */
    private final static long SEQUENCE_BITS = 12L;

    /**
     * 机器ID偏左移12位
     */
    private final static long WORKER_ID_SHIFT = SEQUENCE_BITS;

    /**
     * 数据中心ID左移17位
     */
    private final static long DATACENTER_ID_SHIFT = SEQUENCE_BITS + WORKER_ID_BITS;

    /**
     * 时间毫秒左移22位
     */
    private final static long TIMESTAMP_LEFT_SHIFT = SEQUENCE_BITS + WORKER_ID_BITS + DATACENTER_ID_BITS;

    /**
     * Sequence掩码4095（0b111111111111=0xfff=4095）
     */
    private final static long SEQUENCE_MASK = -1L ^ (-1L << SEQUENCE_BITS);

    /**
     * 上次生产id时间戳
     */
    private static long lastTimestamp = -1L;

    /**
     * 毫秒内Sequence(0~4095)
     */
    private long sequence = 0L;

    /**
     * 工作机器ID（0~31）
     */
    private final long workerId;

    /**
     * 数据标识ID（0~31）
     */
    private final long dataCenterId;

    public IdWorker(){
        this.dataCenterId = getDataCenterId(MAX_DATA_CENTER_ID);
        this.workerId = getWorkerId(dataCenterId, MAX_WORKER_ID);
    }

    /**
     *
     * @param workerId 工作机器ID
     * @param dataCenterId 序列号
     */
    public IdWorker(long workerId, long dataCenterId) {
        if (workerId > MAX_WORKER_ID || workerId < 0) {
            throw new IllegalArgumentException(String.format("worker Id can't be greater than %d or less than 0", MAX_WORKER_ID));
        }
        if (dataCenterId > MAX_DATA_CENTER_ID || dataCenterId < 0) {
            throw new IllegalArgumentException(String.format("data center Id can't be greater than %d or less than 0", MAX_DATA_CENTER_ID));
        }
        this.workerId = workerId;
        this.dataCenterId = dataCenterId;
    }
    /**
     * 获取下一个ID
     *
     * @return
     */
    public synchronized long nextId() {
        long timestamp = timeGen();
        if (timestamp < lastTimestamp) {
            //时钟回拨的情况下抛出异常
            throw new RuntimeException(String.format("Clock moved backwards.  Refusing to generate id for %d milliseconds", lastTimestamp - timestamp));
        }

        //如果是同一时间生成的，则进行毫秒内序列
        if (lastTimestamp == timestamp) {
            // 当前毫秒内，则+1
            sequence = (sequence + 1) & SEQUENCE_MASK;
            //毫秒内序列溢出
            if (sequence == 0) {
                // 当前毫秒内计数满了,阻塞到下一个毫秒,获得新的时间戳
                timestamp = tilNextMillis(lastTimestamp);
            }
        } else {
            //时间戳改变,毫秒内序列重置
            sequence = 0L;
        }
        lastTimestamp = timestamp;
        // ID偏移组合生成最终的ID，并返回ID
        long nextId = ((timestamp - TW_EPOCH) << TIMESTAMP_LEFT_SHIFT)
                | (dataCenterId << DATACENTER_ID_SHIFT)
                | (workerId << WORKER_ID_SHIFT) | sequence;

        return nextId;
    }

    private long tilNextMillis(final long lastTimestamp) {
        long timestamp = this.timeGen();
        while (timestamp <= lastTimestamp) {
            timestamp = this.timeGen();
        }
        return timestamp;
    }

    private long timeGen() {
        return System.currentTimeMillis();
    }

    /**
     * 获取机器id标识
     * @param dataCenterId 数据中心id
     * @param maxWorkerId 机器ID最大值
     * @return
     */
    protected static long getWorkerId(long dataCenterId, long maxWorkerId) {
        StringBuffer mPid = new StringBuffer();
        mPid.append(dataCenterId);
        String name = ManagementFactory.getRuntimeMXBean().getName();
        if (!name.isEmpty()) {
            // GET jvm Pid
            mPid.append(name.split("@")[0]);
        }
        //MAC + PID 的 hashcode 获取16个低位
        return (mPid.toString().hashCode() & 0xffff) % (maxWorkerId + 1);
    }

    /**
     * 获取数据标识id部分
     * @param maxDataCenterId 数据中心最大值
     * @return
     */
    protected static long getDataCenterId(long maxDataCenterId) {
        long id = 0L;
        try {
            InetAddress ip = InetAddress.getLocalHost();
            NetworkInterface network = NetworkInterface.getByInetAddress(ip);
            if (network == null) {
                id = 1L;
            } else {
                byte[] mac = network.getHardwareAddress();
                id = ((0x000000FF & (long) mac[mac.length - 1])
                        | (0x0000FF00 & (((long) mac[mac.length - 2]) << 8))) >> 6;
                id = id % (maxDataCenterId + 1);
            }
        } catch (Exception e) {
            System.out.println(" get dataCenterId: " + e.getMessage());
        }
        return id;
    }

}
