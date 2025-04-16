# IT Skills

- Debian 12 "Bookworm":
  [download](https://www.debian.org/distrib/),
  [installation](https://www.debian.org/releases/stable/arm64/),
  [reference](https://www.debian.org/doc/manuals/debian-reference/)
  - [console](https://wiki.debian.org/Console),
    fonts ([kbd](https://packages.debian.org/bookworm/kbd)),
    locale
  - [bash](https://wiki.debian.org/Bash)
  - [coreutils](https://wiki.debian.org/coreutils)
  - [screen](https://wiki.debian.org/screen)

```sh
ssh sehors # macOS 15.0.1
sudo port install qemu
cd k8s

diskutil apfs resizeContainer

script -a diskutil.script diskutil list
script -a diskutil.script diskutil apfs list
script -a diskutil.script diskutil listFilesystems

diskutil apfs resizeContainer disk3 400G 'Free Space' k8s 0

script -a diskutil.script diskutil list

diskutil addPartition disk0s2 %$(uuidgen)% %noformat% 0
# B9E66621-2D92-4D53-AD3B-3D1C95BCBC33   594.5 GB   disk0s6
# Apple_Boot   134.2 MB   disk0s4
script -a diskutil.script diskutil list



cat <<EOF > user-data 
#cloud-config
password: password
chpasswd:
  expire: False
EOF

cat <<EOF > meta-data
instance-id: someid/somehostname
EOF

touch vendor-data



wget "https://cloud.debian.org/images/cloud/bookworm/latest/debian-12-nocloud-arm64.qcow2"
qemu-system-aarch64 -machine help | less
qemu-system-aarch64 -m 1024 -net nic -net user \
  -drive file=jammy-server-cloudimg-amd64.img,index=0,format=qcow2,media=disk \
  -drive file=seed.img,index=1,media=cdrom \
  -machine accel=kvm:tcg

# https://www.qemu.org/docs/master/system/qemu-manpage.html
# https://www.qemu.org/docs/master/system/arm/vmapple.html
qemu-system-aarch64 \
  -machine virt,accel=hvf,graphics=off,iommu=smmuv3,usb=off \
  -m 2G \
  -drive file=debian-12-nocloud-arm64.qcow2,if=virtio,media=disk \
  -serial mon:stdio -display none
# Ctrl-a a x
qemu-system-aarch64 \
  -machine virt,accel=hvf \
  -m 2G \
  -drive file=debian-12-nocloud-arm64.qcow2,if=virtio,media=disk \
  -serial mon:stdio -display none

# The live CD is graphical
wget "https://cdimage.debian.org/debian-cd/current-live/amd64/iso-hybrid/debian-live-12.10.0-amd64-standard.iso"

wget "https://cdimage.debian.org/debian-cd/current/arm64/iso-cd/debian-12.10.0-arm64-netinst.iso"
qemu-system-aarch64 \
  -m 1G -machine virt,accel=hvf \
  -cdrom debian-12.10.0-arm64-netinst.iso \
  -bios /opt/local/share/qemu/edk2-aarch64-code.fd \
  -boot menu=on \
  -serial mon:stdio -display none -nographic
  # -serial stdio
  # -serial mon:stdio -display none -nographic

qemu-system-aarch64 \
  -m 1G -cpu host -machine virt,accel=hvf,graphics=off,usb=off \
  -cdrom debian-12.10.0-arm64-netinst.iso \
  -bios edk2-aarch64-code.fd \
  -monitor none -serial stdio -nographic \
  -no-reboot -nodefaults
```

Locally,
```sh
port variants qemu
sudo port install qemu -{curses,spice,target_{i386,x86_64},usb,vnc} +{cocoa,target_arm}
cd ~/qemu-help
qemu-system-aarch64 \
  -m 2G -machine virt,accel=hvf \
  -cdrom debian-12.10.0-arm64-netinst.iso \
  -bios /opt/local/share/qemu/edk2-aarch64-code.fd \
  -boot menu=on \
  -serial stdio -display none -nographic
qemu-system-aarch64 \
  -m 1G -cpu cortex-a710 -machine virt,accel=hvf \
  -cdrom debian-12.10.0-arm64-netinst.iso \
  -bios /opt/local/share/qemu/edk2-aarch64-code.fd \
  -monitor none -serial stdio -nographic

# https://news.ycombinator.com/item?id=19736722
# https://github.com/qemu/qemu/blob/master/docs/config/mach-virt-serial.cfg
# https://dev.to/krjakbrjak/qemu-networking-on-macos-549k
# https://www.qemu.org/docs/master/interop/qemu-qmp-ref.html#object-QMP-net.NetdevVmnetBridgedOptions
# https://gitlab.com/qemu-project/qemu/-/issues/1364
# host max cortex-a72 cortex-a76 cortex-a710 a64fx
sudo qemu-system-aarch64 \
  -m 1G -cpu host -machine virt,accel=hvf,graphics=off,usb=off \
  -bios edk2-aarch64-code.fd \
  -cdrom debian-12.10.0-arm64-netinst.iso \
  -netdev vmnet-bridged,id=eth0,ifname=en7 \
  -device virtio-net,netdev=eth0 \
  -monitor none -serial stdio -display none -nographic \
  -no-reboot -nodefaults -no-user-config

qemu-system-aarch64 \
  -m 1G -cpu host -machine virt,accel=hvf,usb=off \
  -cdrom debian-live-12.10.0-amd64-standard.iso \
  -bios edk2-aarch64-code.fd \
  -monitor none \
  -no-reboot

qemu-system-aarch64 \
  -cpu host -machine virt,accel=hvf,graphics=off,usb=off \
  -bios edk2-aarch64-code.fd \
  -writeconfig \
  -monitor none -serial stdio -display none -nographic \
  -no-reboot -nodefaults -no-user-config

qemu-system-aarch64 -machine virt -cpu help | code -
# The valid models are: cortex-a7, cortex-a15, cortex-a35, cortex-a55, cortex-a72, cortex-a76, cortex-a710, a64fx, neoverse-n1, neoverse-v1, neoverse-n2, cortex-a53, cortex-a57, host, max

# https://superuser.com/questions/1684886/qemu-aarch64-on-arm-mac-never-boots-and-only-shows-qemu-prompt
qemu-system-aarch64 \
  -M virt,highmem=off \
  -accel hvf \
  -m 1G \
  -cdrom debian-12.10.0-arm64-netinst.iso \
  -boot d \
  -bios /opt/local/share/qemu/edk2-aarch64-code.fd \
  -serial stdio \
  -boot menu=off \
  -cpu cortex-a72 \
  -nodefaults
```

- NTP (chrony)
- IPv6, SLAAC, DHCPv6
- UEFI (EDK II), PXE (iPXE), systemd-boot
- LVM, LUKS, ext4, fstab
- iproute2, netfilter (nftables), systemd-networkd
- DNS, DNSSEC, DNS over TLS (DoT), DNS over HTTPS (DoH), systemd-resolved, NSS
- IKEv2/IPsec
- LDAP (OpenLDAP/LMDB), GSSAPI (Kerberos V5), SSSD
- SSH (OpenSSH)
- HTTP/3, QUIC, TLSv1.3 (OpenSSL 3.0), nginx
- LVS (IPVS), HAProxy

- Ceph
- eBPF
- KVM, QEMU, libvirt, binfmt_misc, systemd-binfmt
- BGP
- ASN.1
- compiler, linker, binutils
- coreutils, BASH
- PostgreSQL
- Kubernetes
- Visual Studio Code
- openvswitch
- DPDK
- chroot, LXC, Incus
- capabilities, namespaces, seccomp
- ACL, SELinux
- Email
- Lean4
- PKIX, X.509, CA Cert
- curl, wget
- Debian
